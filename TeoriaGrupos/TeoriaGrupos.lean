-- This module serves as the root of the `TeoriaGrupos` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.ModEq

/- Definimos lo que es un grupo-/
class Grupo (G : Type _) extends Mul G, One G, Inv G where

  oper_asociativa : ∀ x y z : G, x * (y * z) = (x * y) * z
  oper_neutro : ∀ x : G, x * 1 = x
  neutro_oper : ∀ x : G, 1 * x = x

  oper_inv : ∀ x : G , (x⁻¹) * x = 1
  inv_oper : ∀ x : G , x * (x⁻¹) = 1


/- Definimos tambien lo que es un grupo abeliano-/
class GrupoAbeliano (G : Type _) extends Grupo G where
  oper_conmutativa : ∀ x y : G, x * y = y * x


/- Varias propiedades de los grupos-/

namespace Grupo /- para no escribir todo el rato Grupo.operacion-/

/-Cancelación-/
theorem oper_cancel_dcha {G} [Grupo G] (a b c : G) :  a * c = b * c → a = b := by
 intro h
 have h1 : (a * c) * (c⁻¹) = (b * c) * (c⁻¹) := by rw[h]
 rw [← oper_asociativa, ← oper_asociativa] at h1
 rw[inv_oper, oper_neutro, oper_neutro] at h1
 exact h1




theorem oper_cancel_izq {G} [Grupo G] (a b c : G) : c * a = c * b → a = b := by
 intro h
 have h1 : (c⁻¹) * (c * a)  = (c⁻¹) * (c * b) := by rw[h]
 rw [oper_asociativa, oper_asociativa] at h1
 rw[oper_inv, neutro_oper,neutro_oper] at h1
 exact h1


/- Ahora vamos a probar la unicidad del neutro y del inverso para cada elemento-/

theorem neutro_unico [Grupo G] (e' : G) (hip1: ∀ x : G, e' * x = x) (_ : ∀ x : G, x * e'= x) : e'= 1 := by
  calc e' = e' * 1 := by rw[oper_neutro]
            _ = 1 := by rw[hip1]

/- Queremos que si a*b=e => b= a^-1-/
theorem inv_unico [Grupo G] (a b : G) (h: a * b= 1): b = a⁻¹ := by
  calc b = 1 * b := by rw[neutro_oper]
      _ = ((a⁻¹) * a ) * b := by rw[oper_inv]
      _ = (a⁻¹) * (a * b) := by rw[oper_asociativa]
      _ = a⁻¹ := by rw[h,oper_neutro]


/- (a^-1)^-1 = a-/
theorem inv_inv [Grupo G] (a: G) : (a⁻¹)⁻¹ = a := by
  symm
  apply (inv_unico)
  rw[oper_inv]

/- (ab)^-1 = b^-1*a^-1-/
theorem inv_compuesto [Grupo G] (a b : G) : (a * b)⁻¹ =  (b⁻¹) * (a⁻¹) := by
  symm
  apply inv_unico
  calc  (a * b) * ((b⁻¹) * (a⁻¹)) = (a * (b * (b⁻¹))) * (a⁻¹) := by simp[oper_asociativa]
                                             _ = a * (a⁻¹) := by rw[inv_oper b, oper_neutro]
                                             _ = 1 := by rw[inv_oper]


/-e^-1 = e-/
theorem inv_neutro  [Grupo G] : (1:G)⁻¹ = 1 := by
  symm
  apply inv_unico
  rw[oper_neutro]


 /- Definimos ahora lo que es la potencia de un elemento-/
/- Por induccion para caso 0 y n-/
/- a^(n+1) = a^n * a-/

def potencia {G} [Grupo G] (a : G) : Nat → G
  | 0 => 1
  | (n+1) =>  a * (potencia a n)

instance {G : Type _} [Grupo G] : Pow G Nat where
  pow a n := potencia a n

@[simp]
theorem pow_zero [Grupo G] (a : G) : a ^ 0 = 1 := rfl

@[simp]
theorem pow_succ [Grupo G] (a : G) (n : Nat) : a ^ (n + 1) = a * (a ^ n) := rfl


/-Aqui demostramos que a^(n+m) = a^n * a^m-/
theorem potencia_suma [Grupo G] (a :G) (n m : Nat) :  a ^ (n+m) = (a ^ n) * (a ^ m) := by
  induction n with
  |zero =>
   simp
   rw[neutro_oper]

  |succ n hn =>
   simp
   calc a ^ (n + 1 + m) = a ^ (n + m + 1) := by rw [Nat.add_right_comm]
                            _  = a *(a ^ (n + m)) := by rfl
   rw[hn]
   rw[oper_asociativa]


/- (a^n)^m = a^n*m-/
theorem potencia_mul [Grupo G] (a : G) (n m : Nat) : a ^ (n*m) = (a ^ n) ^ m := by
  induction m with
  |zero =>
   simp

  | succ m hm =>
   simp
   calc a ^ (n * (m + 1)) = a ^ (n + (n*m)) := by rw [Nat.mul_add_one, Nat.add_comm]
                               _ =  (a ^ n) * (a ^ (n*m)) := by rw[potencia_suma]
   rw[hm]


/- (a*b)^n = a^n * b^n--/
theorem potencia_conmutativa [GrupoAbeliano G] (a b : G) (n : Nat) : (a * b) ^ n =  (a ^ n) * (b ^ n) := by
  induction n with
  |zero =>
    simp
    rw[oper_neutro]

  |succ n hn =>
    simp
    rw[hn]
    calc  (a * b) * ((a ^ n) * (b ^ n)) =  (a * (b * (a ^ n))) * (b ^ n) := by simp[oper_asociativa]
                                                            _ = (a * ((a ^ n) * b)) * (b ^ n) := by rw[GrupoAbeliano.oper_conmutativa b (a ^ n)] /- aqui necesitamos que el grupo sea abeliano-/
                                                            _ =  a * ((a ^ n) * (b * (b ^ n))) := by simp[← oper_asociativa]
                                                            _ = (a * (a ^ n)) * (b * (b ^ n)) := by rw[oper_asociativa]



/- a^-n = ^(a^-1)n-/

theorem potencia_inv [Grupo G] (a : G) (n: Nat) : (a ^ n)⁻¹ = (a⁻¹) ^ n := by
  induction n with
  |zero =>
    simp
    rw[inv_neutro]
  |succ n hn =>
    simp
    rw[inv_compuesto]
    rw[hn]
    calc ((a⁻¹) ^ n) * (a⁻¹) = ((a⁻¹) ^ n) * ((a⁻¹) ^ 1) := by simp [oper_neutro]
                                         _ = (a⁻¹) ^ (n + 1) := by rw [← potencia_suma]



/- a^n * a^m = a^m * a^n -/
theorem potencias_conmutan [Grupo G] (a : G) (n m : Nat) :
  (a ^ n) * (a ^ m) = (a ^ m) * (a ^ n) := by
  rw [← potencia_suma, Nat.add_comm, potencia_suma]

/- Si dos elementos conmutan, el inverso de uno tambien conmuta-/
theorem conmutan_inv [Grupo G] {x y : G} (h : x * y = y * x) :
  (x⁻¹) * y = y * (x⁻¹) := by
  apply oper_cancel_izq (c := x)
  rw [oper_asociativa, inv_oper, neutro_oper]
  rw [oper_asociativa]
  rw [h]
  rw [← oper_asociativa]
  rw [inv_oper, oper_neutro]


/-Ahora vamos a definir el orden de un grupo; tenemos que asegurarnos
de que sea finito para poder hacerlo; -/

def orden_grupo (G : Type _) [Grupo G] [Fintype G] : Nat := Fintype.card G

notation "|" G "|" => orden_grupo G

/- Ahora definimos lo que es un subgrupo; con structure y pertenece a la calse de Grupo-/
structure Subgrupo (H : Type _) [Grupo H] where
 /- La funcion que indica los elementos del Grupo están SI o NO-/
 filtro: H → Prop

 neutro_sub : filtro 1
 oper_sub : filtro x → filtro y → filtro (x * y)
 inv_sub : filtro x → filtro (x⁻¹)

instance [Grupo G] (H : Subgrupo G) : Grupo {x : G // H.filtro x} where
  mul x y := ⟨x.1 * y.1, H.oper_sub x.2 y.2⟩
  one := ⟨1, H.neutro_sub⟩
  inv x := ⟨x⁻¹, H.inv_sub x.2⟩

  -- 4. Demostramos que cumple las leyes heredándolas del grupo original
  oper_asociativa x y z := by ext; exact Grupo.oper_asociativa x.1 y.1 z.1
  oper_neutro x := by ext; exact Grupo.oper_neutro x.1
  neutro_oper x := by ext; exact Grupo.neutro_oper x.1
  oper_inv x := by ext; exact Grupo.oper_inv x.1
  inv_oper x := by ext; exact Grupo.inv_oper x.1


/- ALGUNAS PROPIEDADES DE SUBGRUPOS-/
/- Aqui definimos que la interseccion de dos subgrupos es subgrupo-/
def interseccion [Grupo G] (H K : Subgrupo G) : Subgrupo G where
  filtro x := H.filtro x ∧ K.filtro x
  neutro_sub := ⟨H.neutro_sub, K.neutro_sub⟩
  oper_sub hx hy := ⟨H.oper_sub hx.1 hy.1, K.oper_sub hx.2 hy.2⟩
  inv_sub hx := ⟨H.inv_sub hx.1, K.inv_sub hx.2⟩


  /-- Definimos el subgrupo trivial (solo el elemento neutro) -/
def SubgrupoTrivial (G : Type _) [Grupo G] : Subgrupo G where
  filtro x := x = 1
  neutro_sub := rfl
  oper_sub hx hy := by rw [hx, hy, Grupo.oper_neutro]
  inv_sub hx := by rw [hx, Grupo.inv_neutro]

/-- Definimos el subgrupo total G -/
def SubgrupoTotal (G : Type _) [Grupo G] : Subgrupo G where
  filtro _ := True
  neutro_sub := trivial
  oper_sub _ _ := trivial
  inv_sub _ := trivial

/-- Definición de subgrupo propio: No es el trivial ni el total -/
def EsSubgrupoPropio [Grupo G] (H : Subgrupo G) : Prop :=
  H ≠ SubgrupoTrivial G ∧ H ≠ SubgrupoTotal G



/-Aqui definimos Grupo ciclico-/
def EsCiclico [Grupo G] (H : Subgrupo G) : Prop :=
  ∃ a : G, ∀ x : G, H.filtro x ↔ (∃ n : Nat, x = a ^ n ∨ x = (a⁻¹) ^ n)


/-Subgrupo generado por un subconjunto S. Es el menor subgrupo que contiene a todos los elementos que cumplen S. -/
def SubgrupoGenerado [Grupo G] (S : G → Prop) : Subgrupo G where
  filtro x := ∀ (H : Subgrupo G), (∀ s : G, S s → H.filtro s) → H.filtro x

  neutro_sub H _ := H.neutro_sub
  oper_sub hx hy H hS := H.oper_sub (hx H hS) (hy H hS)
  inv_sub hx H hS := H.inv_sub (hx H hS)


/- Demostramos que todo grupo ciclico esa abeliano-/
theorem ciclico_es_abeliano [Grupo G] (H : Subgrupo G) (h: EsCiclico H) :
  ∀ x y, H.filtro x → H.filtro y → x * y = y * x := by
  obtain ⟨a, h_gen⟩ := h
  intro x y hx hy
  rw [h_gen] at hx hy

  obtain ⟨n, (rfl | hx_inv)⟩ := hx
  · -- Caso x = aⁿ
    obtain ⟨m, (rfl | hy_inv)⟩ := hy
    · apply potencias_conmutan
    · rw [hy_inv, ← potencia_inv] --
      symm
      apply conmutan_inv
      apply potencias_conmutan
  · -- Caso x = (a⁻¹)ⁿ
    rw [hx_inv, ← potencia_inv]
    obtain ⟨m, (rfl | hy_inv)⟩ := hy
    · apply conmutan_inv
      apply potencias_conmutan
    · rw [hy_inv, ← potencia_inv]
      apply conmutan_inv
      symm
      apply conmutan_inv
      symm
      apply potencias_conmutan



/-- El subgrupo generado por un elemento 'a' es el menor subgrupo que contiene a 'a' -/
def SubgrupoGeneradoPor [Grupo G] (a : G) : Subgrupo G := SubgrupoGenerado (λ x => x = a)

notation "⟨" a "⟩" => SubgrupoGeneradoPor a


/-- n es un exponente positivo que devuelve el elemento al neutro -/
def se_anula_en [Grupo G] (a : G) (n : Nat) : Prop :=
  n > 0 ∧ a ^ n = 1


/-- Definimos el orden de un elemento como el minimo n ∈ ℕ tal que a^n = e. -/
def EsOrdenDe [Grupo G] (a : G) (n : Nat) : Prop :=
  se_anula_en a n ∧ ∀ m : Nat, se_anula_en a m → n ≤ m


/- ord(a) = 1 ↔ a = e -/
theorem orden_uno_si_neutro [Grupo G] (a : G) : EsOrdenDe a 1 ↔ a = 1 :=
  by
  constructor
  · -- Si el orden es 1, entonces a = neutro
    intro h
    have h_anul := h.left
    have h_pot := h_anul.right

    dsimp [potencia] at h_pot
    rw [Grupo.oper_neutro] at h_pot
    exact h_pot
  · intro h
    rw [h]
    constructor
    · -- Demostrar que se anula en 1
      constructor
      · decide -- Lean sabe automáticamente que 1 > 0
      · dsimp [potencia]
        rw [Grupo.oper_neutro]
    · -- Demostrar que es el mínimo
      intro m hm
      have hm_pos := hm.left -- Extraemos que m > 0
      exact hm_pos -- En Lean, decir m > 0 para naturales es exactamente 1 ≤ m


/- Primero un lema auxiliar para probar que ord(a) = ord(a⁻¹).  -/
theorem se_anula_en_inv [Grupo G] (a : G) (n : Nat) :
  se_anula_en a n ↔ se_anula_en (a⁻¹) n := by
  constructor
  · intro h
    constructor
    · exact h.left
    · rw [← potencia_inv, h.right, Grupo.inv_neutro]
  · intro h
    constructor
    · exact h.left
    · -- Tenemos que (a⁻¹)ⁿ = e. Queremos aⁿ = e.
      have h2 := h.right
      rw [← potencia_inv] at h2
      have h3 : ((a ^ n)⁻¹)⁻¹ = 1⁻¹ := by rw [h2]
      rw [Grupo.inv_inv, Grupo.inv_neutro] at h3
      exact h3


/- ord(a) = ord(a⁻¹) -/
theorem orden_inv [Grupo G] (a : G) (n : Nat) :
  EsOrdenDe a n ↔ EsOrdenDe (a⁻¹) n := by
  constructor
  · intro h
    constructor
    · rw [← se_anula_en_inv]
      exact h.left
    · intro m hm
      apply h.right
      rw [se_anula_en_inv]
      exact hm
  · intro h
    constructor
    · rw [se_anula_en_inv]
      exact h.left
    · intro m hm
      apply h.right
      rw [← se_anula_en_inv]
      exact hm


/- Lema auxiliar: (b * a * b⁻¹)ⁿ = b * aⁿ * b⁻¹ -/
theorem potencia_conjugado [Grupo G] (a b : G) (n : Nat) :
  ((b * a) * (b⁻¹)) ^ n =
  (b * (a ^ n)) * (b⁻¹) := by
  induction n with
  | zero =>
    simp
    rw [Grupo.oper_neutro, Grupo.inv_oper]
  | succ n hn =>
    simp
    rw [hn]
    calc
      ((b * a) * b⁻¹) * ((b * a ^ n) * b⁻¹) = (b * a) * (b⁻¹ * ((b * a ^ n) * b⁻¹)) := by rw [← Grupo.oper_asociativa]
                                                _  = (b * a) * ((b⁻¹ * (b * a ^ n)) * b⁻¹) := by rw [Grupo.oper_asociativa b⁻¹ _ _]
                                                _  = ((b * a) * (b⁻¹ * (b * a ^ n))) * b⁻¹ := by rw [Grupo.oper_asociativa]
                                                _  = ((b * a) * ((b⁻¹ * b) * a ^ n)) * b⁻¹ := by rw [← Grupo.oper_asociativa b⁻¹ b _]
                                                _  = ((b * a) * (1 * a ^ n)) * b⁻¹ := by rw [Grupo.oper_inv]
                                                _  = ((b * a) * a ^ n) * b⁻¹ := by rw [Grupo.neutro_oper] -- (O one_oper si lo renombraste)
                                                _  = (b * (a * a ^ n)) * b⁻¹ := by rw [Grupo.oper_asociativa b a _]


/- a se anula en n ↔ (b a b⁻¹) se anula en n -/
theorem se_anula_en_conjugado [Grupo G] (a b : G) (n : Nat) :
  se_anula_en a n ↔ se_anula_en ((b * a) * (b⁻¹)) n := by
  constructor
  · intro h
    constructor
    · exact h.left
    · rw [potencia_conjugado, h.right, Grupo.oper_neutro, Grupo.inv_oper]
  · intro h
    constructor
    · exact h.left
    · have h2 := h.right
      rw [potencia_conjugado] at h2
      -- b * aⁿ * b⁻¹ =  e
      have h3 : b * (a ^ n) = b * 1 := by
        have h2' : (b * (a ^ n)) * (b⁻¹) =
                   (b * 1) * (b⁻¹) := by rw [h2]; rw [Grupo.oper_neutro, Grupo.inv_oper]
        exact Grupo.oper_cancel_dcha (b * (a ^ n)) (b * 1) (b⁻¹) h2'
      have h4 : a ^ n = 1 :=
        Grupo.oper_cancel_izq (a ^ n) 1 b h3
      exact h4


/-ord(b a b⁻¹) = ord(a) -/
theorem orden_conjugado [Grupo G] (a b : G) (n : Nat) :
  EsOrdenDe a n ↔ EsOrdenDe ((b * a) * (b⁻¹)) n := by
  constructor
  · intro h
    constructor
    · rw [← se_anula_en_conjugado]
      exact h.left
    · intro m hm
      apply h.right
      rw [se_anula_en_conjugado]
      exact hm
  · intro h
    constructor
    · rw [se_anula_en_conjugado]
      exact h.left
    · intro m hm
      apply h.right
      rw [← se_anula_en_conjugado]
      exact hm



/- Un elemento tiene orden infinito si NO existe n > 0 tal que aⁿ = e -/
def OrdenInfinito [Grupo G] (a : G) : Prop :=
  ∀ n : Nat, ¬(n > 0 ∧ a ^ n = 1)

/- si aⁱ = aʲ con i ≠ j entonces existe k > 0 tal que aᵏ = e -/
theorem potencias_iguales_finito [Grupo G] (a : G) (i j : Nat) (h_eq : a ^ i = a ^ j) (h_ne : i ≠ j) :
  ∃ k : Nat, k > 0 ∧ a ^ k = 1 := by
  -- Sin pérdida de generalidad, supongamos i > j
  by_cases hij : i > j
  · use i - j
    constructor
    · omega
    · /-a^i = a^(i-j) * a^j-/
      have h1 : a ^ i = (a ^ (i - j)) * (a ^ j) := by
        rw [← potencia_suma]; congr 1; omega
      rw [h1] at h_eq
      -- Entonces (a^(i-j)) * a^j = a^j
      have h2 : (a ^ (i - j)) * (a ^ j) = a ^ j := h_eq
      apply oper_cancel_dcha (a ^ (i - j)) 1 (a ^ j)
      rw [neutro_oper]
      exact h2

  · -- Caso j ≥ i, pero como i ≠ j,  j > i
    push_neg at hij
    have hji : j > i := by omega
    use j - i
    constructor
    · omega
    · have h1: a ^ j = (a ^ (j - i)) * (a ^ i) := by
        rw [← potencia_suma]; congr 1; omega
      rw [h1] at h_eq
      apply oper_cancel_dcha (a ^ (j - i)) 1 (a ^ i)
      simp [neutro_oper]
      exact h_eq.symm



/-Si a tiene orden n y aᵏ = e, entonces n | k -/
theorem division_exponentes [Grupo G] (a : G) (n k : Nat) (h_orden : EsOrdenDe a n) (h_k : a ^ k = 1) : n ∣ k := by
  -- Por el algoritmo de división: k = nq + r con 0 ≤ r < n
  have hn_pos : n > 0 := h_orden.left.1

  -- Demostramos por contradicción: supongamos que n ∤ k
  by_contra h_ndiv

  -- Si n ∤ k, entonces k % n ≠ 0, y k % n > 0
  have h_r_pos : k % n > 0 := by
    have : k % n ≠ 0 := by
      intro h_eq
      have h2: n ∣ k := Nat.dvd_of_mod_eq_zero h_eq
      exact h_ndiv h2
    exact Nat.pos_of_ne_zero this

  have hk_div : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm

  -- a^k = a^(nq + r) = a^(nq) * a^r (por potencia_suma)
  have h_ar : a ^ (k % n) = 1 := by
    have h_decomp : a ^ k = (a ^ (n * (k / n))) * (a ^ (k % n)) := by
      calc a ^ k = a ^ (n * (k / n) + k % n) := by rw [← hk_div]
                      _ = (a ^ (n * (k / n))) * (a ^ (k % n)) := potencia_suma a _ _

    -- (a^n)^q = 1^q = 1 (potencia de 1 es 1)
    have h_an : a ^ n = 1 := h_orden.left.2
    have h_anq : a ^ (n * (k / n)) = 1 := by
      rw [potencia_mul, h_an]
      -- Probamos que potencia 1 q = 1
      -- Demostración por inducción en q = k/n
      have hfin : ∀ (q : Nat), (1:G) ^ q = 1 := by
        intro q
        induction q with
        | zero => simp
        | succ m hm =>
          rw [pow_succ]
          rw [hm]
          rw [oper_neutro]
      exact hfin (k / n)

    -- Si 1 * a^r = 1 entonces a^r = 1
    rw [h_decomp, h_anq] at h_k
    rw [neutro_oper] at h_k
    exact h_k

  -- Pero esto es contradictorio
  have h_min : n ≤ k % n := h_orden.right (k % n) ⟨h_r_pos, h_ar⟩
  have h_menor : k % n < n := Nat.mod_lt k (by omega)
  omega




/-CONGRUENCIAS MODULO DE UN SUBUGRPO -/


/-- Relación de congruencia por la derecha: a ~ b si a⁻¹ * b ∈ H -/
def RelDcha [Grupo G] (H : Subgrupo G) (a b : G) : Prop :=
  H.filtro ((a⁻¹) * b)

/-- Relación de congruencia por la izquierda: a ~ b si b * a⁻¹ ∈ H -/
def RelIzq [Grupo G] (H : Subgrupo G) (a b : G) : Prop :=
  H.filtro (b * (a⁻¹))


theorem relDcha_es_equivalencia [Grupo G] (H : Subgrupo G) :
    Equivalence (RelDcha H) := {
  -- Reflexividad: a ~ a => a⁻¹ * a = e ∈ H
  refl := by
    intro a
    dsimp [RelDcha]
    rw [oper_inv]
    exact H.neutro_sub

  -- Simetría: a ~ b => b ~ a (si a⁻¹ * b ∈ H, entonces (a⁻¹ * b)⁻¹ = b⁻¹ * a ∈ H)
  symm :=by
    intro a b h
    dsimp [RelDcha] at *
    have h_inv := H.inv_sub h
    rw [inv_compuesto, inv_inv] at h_inv
    exact h_inv

  -- Transitividad: a ~ b y b ~ c => a ~ c
  trans := by
    intro a b c hab hbc
    dsimp [RelDcha] at *
    -- Tenemos a⁻¹ * b ∈ H y b⁻¹ * c ∈ H, multiplicamos: (a⁻¹ * b) * (b⁻¹ * c)
    have h_prod := H.oper_sub hab hbc
    rw [← oper_asociativa, oper_asociativa b, inv_oper, neutro_oper] at h_prod
    exact h_prod
}


theorem relIzq_es_equivalencia {G} [Grupo G] (H : Subgrupo G) :
  Equivalence (RelIzq H) := {
  -- Reflexividad: a ~ a => a * a⁻¹ = e ∈ H
  refl := by
    intro a
    dsimp [RelIzq]
    rw [inv_oper] -- Propiedad a * a⁻¹ = e
    exact H.neutro_sub -- El neutro pertenece al subgrupo

  -- Simetría: a ~ b => b ~ a (si a * b⁻¹ ∈ H, entonces (a * b⁻¹)⁻¹ = b * a⁻¹ ∈ H)
  symm := by
    intro a b h
    dsimp [RelIzq] at *
    have h_inv := H.inv_sub h -- Si x ∈ H, entonces x⁻¹ ∈ H
    -- Aplicamos (a * b⁻¹)⁻¹ = (b⁻¹)⁻¹ * a⁻¹ = b * a⁻¹
    rw [inv_compuesto, inv_inv] at h_inv
    exact h_inv

  -- Transitividad: a ~ b y b ~ c => a ~ c
  trans := by
    intro a b c hab hbc
    dsimp [RelIzq] at *
    -- Tenemos c * b⁻¹ ∈ H y b * a⁻¹ ∈ H, multiplicamos: (c * b⁻¹) * (b * a⁻¹)
    have h_prod := H.oper_sub hbc hab -- Cerrado bajo la operación
    -- Simplificamos: (c * b⁻¹) * (b * a⁻¹) = c * (b⁻¹ * b) * a⁻¹ = c * 1 * a⁻¹ = c * a⁻¹
    rw [← oper_asociativa, oper_asociativa (b⁻¹), oper_inv, neutro_oper] at h_prod
    exact h_prod
}


-- Definición de la Clase Lateral Derecha: aH = {ah | h ∈ H}
def ClaseDcha [Grupo G] (H : Subgrupo G) (a : G) : Set G :=
  {b | RelDcha H a b}

-- Definición de la Clase Lateral Izquierda: Ha = {ha | h ∈ H}
def ClaseIzq [Grupo G] (H : Subgrupo G) (a : G) : Set G :=
  {b | RelIzq H a b}





open Classical

/-- Cada clase lateral derecha es equivalente al subgrupo H -/
def equiv_claseDcha {G} [Grupo G] (H : Subgrupo G) (a : G) :
    ClaseDcha H a ≃ {x // H.filtro x} :=
  { toFun := fun x => ⟨(a⁻¹) * x.val, x.property⟩
    invFun := fun h => ⟨a * h.val, by
      dsimp [RelDcha, ClaseDcha]
      rw [Grupo.oper_asociativa, Grupo.oper_inv, Grupo.neutro_oper]
      exact h.property⟩
    left_inv := fun x => Subtype.ext (by dsimp; rw [Grupo.oper_asociativa, Grupo.inv_oper, Grupo.neutro_oper])
    right_inv := fun h => Subtype.ext (by dsimp; rw [Grupo.oper_asociativa, Grupo.oper_inv, Grupo.neutro_oper]) }

/-- card(aH) = |H| -/
theorem card_claseDcha_eq_card_H {G} [Grupo G] [Fintype G] (H : Subgrupo G) (a : G) :
    Fintype.card (ClaseDcha H a) = Fintype.card {x // H.filtro x} := by
  exact Fintype.card_congr (equiv_claseDcha H a)


/- card(Ha) = |H| es de forma analoga -/
theorem card_claseIzq_eq_card_H {G} [Grupo G] [Fintype G] (H : Subgrupo G) (a : G) :
    Fintype.card (ClaseIzq H a) = Fintype.card {x // H.filtro x} := by
  apply Fintype.card_congr
  -- Construimos la biyección
  exact {
    -- f(x) = x * a⁻¹. (Como x está en aH, a⁻¹*x ya está en H por definición)
    toFun := fun x => ⟨x.val * (a⁻¹), x.property⟩

    -- f⁻¹(h) = h * a.
    invFun := fun h => ⟨ h.val * a, by
      dsimp [RelIzq, ClaseIzq]
      rw [← Grupo.oper_asociativa,Grupo.inv_oper, Grupo.oper_neutro]
      exact h.property⟩

    --  f⁻¹(f(x)) = x  => (x * a⁻¹) * a= x
    left_inv := fun x => Subtype.ext (by
      dsimp
      rw [← Grupo.oper_asociativa, Grupo.oper_inv , Grupo.oper_neutro])

    --  f(f⁻¹(h)) = h => a⁻¹ * (a * h) = h
    right_inv := fun h => Subtype.ext (by
      dsimp
      rw [← Grupo.oper_asociativa, Grupo.inv_oper, Grupo.oper_neutro])
  }


/-El número de clases derechas es igual al de izquierdas -/
/- Definimos los Setoid y Quotient -/

def setoidDcha {G} [Grupo G] (H : Subgrupo G) : Setoid G :=
  ⟨RelDcha H, relDcha_es_equivalencia H⟩

def setoidIzq {G} [Grupo G] (H : Subgrupo G) : Setoid G :=
  ⟨RelIzq H, relIzq_es_equivalencia H⟩



theorem card_num_clases_igual {G} [Grupo G] [Fintype G] (H : Subgrupo G) :
    Fintype.card (Quotient (setoidIzq H)) = Fintype.card (Quotient (setoidDcha H)) := by
  -- 1. Usamos la congruencia de cardinalidad para tipos finitos
  apply Fintype.card_congr

  -- 2. Definimos la biyección base f(x) = x⁻¹ en el grupo G
  let biy_inv : G ≃ G := {
    toFun := fun x => x⁻¹
    invFun := fun x => x⁻¹
    left_inv := Grupo.inv_inv
    right_inv := Grupo.inv_inv
  }

  -- a ~ b (Izq) ↔ f(a) ~ f(b) (Dcha)
  apply Quotient.congr biy_inv

  intro a b
  dsimp [setoidIzq, setoidDcha, RelIzq, RelDcha]

  constructor
  · intro h
    -- Si a⁻¹ * b ∈ H, entonces su inverso también está en H
    let h_inv := H.inv_sub h
    rw [Grupo.inv_compuesto, Grupo.inv_inv] at h_inv
    dsimp [biy_inv]
    rw[inv_inv]
    exact h_inv

  · -- Si a * b⁻¹ ∈ H, demostrar que el inverso está en H
    intro h
    let h_inv := H.inv_sub h
    rw [Grupo.inv_compuesto, Grupo.inv_inv] at h_inv
    dsimp [biy_inv] at h_inv
    rw[inv_inv] at h_inv
    exact h_inv


/-Definimos lo que es el indice y añadimos la notación -/
noncomputable def indice {G} [Grupo G] [Fintype G] (H : Subgrupo G) : ℕ :=
  Fintype.card (Quotient (setoidIzq H))

notation "[" G ":" H "]" => @indice G _ _ H

theorem lagrange {G : Type _} [Grupo G] [Fintype G] (H : Subgrupo G) :
    orden_grupo G = Fintype.card {x : G // H.filtro x} * [G : H] := by
  unfold orden_grupo indice
  -- Reescribimos card(H × Q) = card(H) * card(Q)
  rw [← Fintype.card_prod]
  apply Fintype.card_congr
  -- Hay una biyección: G ≃ H × Quotient(setoidIzq H)

  let π : G → Quotient (setoidIzq H) := Quotient.mk (setoidIzq H)
  -- La proyeccion envia un elemento g a su clase lateral izquierda [g]
  exact {
    -- toFun(g)     = (q.out * g⁻¹,  q)   donde q = [g]
    toFun := fun g => -- ⟨(elemento de H, clase lateral)⟩
      ⟨ ⟨(π g).out * g⁻¹, Quotient.exact (Quotient.out_eq (π g)).symm⟩,
       π g ⟩

    -- invFun(h, q) = h⁻¹ * q.out
    invFun := fun ⟨⟨h, _⟩, q⟩ => h⁻¹ * q.out
    -- invFun(toFun(g)) = (q.out * g⁻¹)⁻¹ * q.out
    --                  = (g * q.out⁻¹) * q.out = g

    left_inv := fun g => by
      simp only
      rw [inv_compuesto, inv_inv, ← oper_asociativa, oper_inv, oper_neutro]

    right_inv := fun ⟨⟨h, hh⟩, q⟩ => by
      have hπ : π (h⁻¹ * q.out) = q := by
        have hrel : (setoidIzq H).r (h⁻¹ * q.out) q.out := by
          show RelIzq H (h⁻¹ * q.out) q.out
          unfold RelIzq
          rw [inv_compuesto, inv_inv, oper_asociativa, inv_oper, neutro_oper]
          exact hh
        calc π (h⁻¹ * q.out)
            = π q.out := Quotient.sound hrel
          _ = q       := Quotient.out_eq q
      apply Prod.ext
      · apply Subtype.ext
        simp only
        rw [hπ, inv_compuesto, inv_inv, oper_asociativa, inv_oper, neutro_oper]
      · exact hπ }

/- Relación H ≤ K -/
def SubgrupoContenido {G} [Grupo G] (H K : Subgrupo G) : Prop := ∀ x, H.filtro x → K.filtro x

/- Restricción de H dentro de K -/
def res_sub {G} [Grupo G] (H K : Subgrupo G) : Subgrupo {x // K.filtro x} where
  filtro x := H.filtro x.1
  neutro_sub := H.neutro_sub
  oper_sub hx hy := H.oper_sub hx hy
  inv_sub hx := H.inv_sub hx

/- Teorema de los índices -/
theorem teorema_indices {G} [Grupo G] [Fintype G] (H K : Subgrupo G) (h : SubgrupoContenido H K) : [G : H] = [G : K] * (@indice _ _ _ (res_sub H K)) := by
  -- Biyección de cardinales
  have c : Fintype.card {x // H.filtro x} = Fintype.card {x // (res_sub H K).filtro x} :=
    -- Construimos la biyeccion entre {x // H.filtro x} y {x // (res_sub H K).filtro x}
    Fintype.card_congr ⟨fun x => ⟨⟨x.1, h x.1 x.2⟩, x.2⟩,
     fun x => ⟨x.1.1, x.2⟩,
     fun _ => rfl,
     fun _ => rfl⟩

  -- Cadena de igualdades aplicando Lagrange
  have eq : Fintype.card {x // H.filtro x} * [G : H] = Fintype.card {x // H.filtro x} * ([G : K] * (@indice _ _ _ (res_sub H K))) := by
    calc Fintype.card {x // H.filtro x} * [G : H] = orden_grupo G := (lagrange H).symm
    _ = Fintype.card {x // K.filtro x} * [G : K] := lagrange K
    _ = (Fintype.card {x // (res_sub H K).filtro x} * (@indice _ _ _ (res_sub H K))) * [G : K] := by rw [← lagrange (res_sub H K)]; rfl
    _ = Fintype.card {x // H.filtro x} * ([G : K] * (@indice _ _ _ (res_sub H K))) := by rw [← c, Nat.mul_comm [G : K], ← Nat.mul_assoc]

  -- Cancelamos el cardinal de H a ambos lados
  exact Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.mpr ⟨⟨1, H.neutro_sub⟩⟩) eq
  -- H no esta vacio, ya que el neutro pertenece a H


/-- Un subgrupo H es normal en G (H ⊲ G) si para todo a ∈ G, aH = Ha -/
def EsNormal [Grupo G] (H : Subgrupo G) : Prop :=
  ∀ a : G, ClaseDcha H a = ClaseIzq H a

-- Definimos la notación H ⊲ G para subgrupos normales
notation:50 H " ⊲ " G => @EsNormal G _ H

/-- Un grupo G es simple si no tiene subgrupos normales distintos del trivial {e} -/
def EsSimple (G : Type _) [Grupo G] : Prop :=
  ∀ H : Subgrupo G, (H ⊲ G) → (H = SubgrupoTrivial G)



/-- Si G es abeliano, todo subgrupo es normal -/
theorem subgrupo_abeliano_es_normal [GrupoAbeliano G] (H : Subgrupo G) : H ⊲ G := by
  intro a
  ext b
  -- Demostramos que RelDcha H a b ↔ RelIzq H a b
  dsimp [ClaseDcha, ClaseIzq, RelDcha, RelIzq]
  rw [GrupoAbeliano.oper_conmutativa]



/-- Definimos el producto de dos conjuntos HK = {hk | h ∈ H, k ∈ K} -/
def ProdConjuntos {G} [Grupo G] (H K : Subgrupo G) (x : G) : Prop :=
  ∃ h k, H.filtro h ∧ K.filtro k ∧ x = h * k

/- Condición lógica para que un subconjunto cualquiera forme un subgrupo -/
/- Un subgrupo es un predicado de pertenencia -/
def FormaSubgrupo {G} [Grupo G] (P : G → Prop) : Prop :=
  P 1 ∧ (∀ x y, P x → P y → P (x * y)) ∧ (∀ x, P x → P (x⁻¹))


/- HK es subgrupo ↔ HK = KH -/
theorem hk_igual_kh {G} [Grupo G] (H K : Subgrupo G) : FormaSubgrupo (ProdConjuntos H K) ↔ (∀ x, ProdConjuntos H K x ↔ ProdConjuntos K H x) := by
  constructor
  · -- ⇒ : Si HK es subgrupo, entonces HK = KH
    intro h_sub x
    constructor
    · -- HK ⊆ KH
      intro ⟨h, k, hh, hk, hx⟩
      have hinv : ProdConjuntos H K (x⁻¹) := h_sub.2.2 x ⟨h, k, hh, hk, hx⟩
      rcases hinv with ⟨h₂, k₂, hh₂, hk₂, hxinv⟩
      use k₂⁻¹, h₂⁻¹
      -- Usamos refine para evitar repetir la parte de demostrar que k₂⁻¹ ∈ K y h₂⁻¹ ∈ H
      refine ⟨K.inv_sub hk₂, H.inv_sub hh₂, ?_⟩
      calc x = (x⁻¹)⁻¹ := (Grupo.inv_inv x).symm
           _ = (h₂ * k₂)⁻¹ := by rw [hxinv]
           _ = k₂⁻¹ * h₂⁻¹ := by rw [Grupo.inv_compuesto]
    · -- KH ⊆ HK
      intro ⟨k, h, hk, hh, hx⟩
      have hk_in : ProdConjuntos H K k := ⟨1, k, H.neutro_sub, hk, (Grupo.neutro_oper k).symm⟩
      have hh_in : ProdConjuntos H K h := ⟨h, 1, hh, K.neutro_sub, (Grupo.oper_neutro h).symm⟩
      have hprod := h_sub.2.1 k h hk_in hh_in
      rw [← hx] at hprod
      exact hprod

  · -- ⇐ : Si HK = KH, entonces HK es subgrupo
    intro h_conmutan
    -- Usamos refine para probar las 3 condiciones de ser subgrupo
    refine ⟨?_, ?_, ?_⟩
    · -- Elemento neutro
      use 1, 1
      exact ⟨H.neutro_sub, K.neutro_sub, (Grupo.oper_neutro 1).symm⟩
    · -- Cerrado bajo el producto
      intro x y ⟨h₁, k₁, hh₁, hk₁, hx⟩ ⟨h₂, k₂, hh₂, hk₂, hy⟩
      have hkh : ProdConjuntos K H (k₁ * h₂) := ⟨k₁, h₂, hk₁, hh₂, rfl⟩
      have hkh2 := (h_conmutan (k₁ * h₂)).mpr hkh
      rcases hkh2 with ⟨h₃, k₃, hh₃, hk₃, hkh3⟩
      use (h₁ * h₃), (k₃ * k₂)
      refine ⟨H.oper_sub hh₁ hh₃, K.oper_sub hk₃ hk₂, ?_⟩
      rw [hx, hy]
      calc (h₁ * k₁) * (h₂ * k₂)
        _ = h₁ * (k₁ * (h₂ * k₂)) := by rw [← Grupo.oper_asociativa h₁ k₁ (h₂ * k₂)]
        _ = h₁ * ((k₁ * h₂) * k₂) := by rw [Grupo.oper_asociativa k₁ h₂ k₂]
        _ = h₁ * ((h₃ * k₃) * k₂) := by rw [hkh3]
        _ = h₁ * (h₃ * (k₃ * k₂)) := by rw [← Grupo.oper_asociativa h₃ k₃ k₂]
        _ = (h₁ * h₃) * (k₃ * k₂) := by rw [Grupo.oper_asociativa h₁ h₃ (k₃ * k₂)]
    · -- Cerrado bajo el inverso
      intro x ⟨h, k, hh, hk, hx⟩
      have hinv : ProdConjuntos K H (x⁻¹) := by
        use k⁻¹, h⁻¹
        refine ⟨K.inv_sub hk, H.inv_sub hh, ?_⟩
        rw [hx, Grupo.inv_compuesto]
      exact (h_conmutan (x⁻¹)).mpr hinv



/- Si K ⊲ G y H < G ⇒ HK < G -/
theorem corolario_hk_igual_kh {G} [Grupo G] (H K : Subgrupo G) (hK_norm : K ⊲ G) : FormaSubgrupo (ProdConjuntos H K) := by
  rw [hk_igual_kh]
  intro x
  constructor
  · -- HK ⊆ KH
    intro ⟨h, k, hh, hk, hx⟩
    have hd : (h * k) ∈ ClaseDcha K h := by
      dsimp [ClaseDcha, RelDcha]
      rw [Grupo.oper_asociativa, Grupo.oper_inv, Grupo.neutro_oper]
      exact hk
    have hi : (h * k) ∈ ClaseIzq K h := by rw [← hK_norm h]; exact hd
    dsimp [ClaseIzq, RelIzq] at hi
    use ((h * k) * h⁻¹), h
    -- Usamos refine porque ya tenemos la parte de demostrar que (h * k) * h⁻¹ ∈ H y h ∈ K
    refine ⟨hi, hh, ?_⟩
    symm
    calc ((h * k) * h⁻¹) * h = (h * k) * (h⁻¹ * h) := by rw [← Grupo.oper_asociativa] -- <-- Flecha añadida
      _ = (h * k) * 1 := by rw [Grupo.oper_inv h]
      _ = h * k := by rw [Grupo.oper_neutro (h * k)]
      _ = x := hx.symm

  · -- KH ⊆ HK
    intro ⟨k, h, hk, hh, hx⟩
    have hi : (k * h) ∈ ClaseIzq K h := by
      dsimp [ClaseIzq, RelIzq]
      rw [← Grupo.oper_asociativa, Grupo.inv_oper, Grupo.oper_neutro]
      exact hk
    have hd : (k * h) ∈ ClaseDcha K h := by rw [hK_norm h]; exact hi
    dsimp [ClaseDcha, RelDcha] at hd
    use h, (h⁻¹ * (k * h))
    refine ⟨hh, hd, ?_⟩
    symm
    calc h * (h⁻¹ * (k * h)) = (h * h⁻¹) * (k * h) := by rw [Grupo.oper_asociativa]
      _ = 1 * (k * h) := by rw [Grupo.inv_oper h]
      _ = k * h := by rw [Grupo.neutro_oper]
      _ = x := hx.symm


/-- Un subgrupo normal absorbe las conjugaciones -/
theorem conj_normal {G} [Grupo G] (N : Subgrupo G) (hN : N ⊲ G) (n g : G) (hn : N.filtro n) : N.filtro ((g * n) * g⁻¹) := by
  have hi : (n * g⁻¹) ∈ ClaseIzq N (g⁻¹) := by
    dsimp [ClaseIzq, RelIzq]
    rw [← Grupo.oper_asociativa, Grupo.inv_inv, Grupo.oper_inv, Grupo.oper_neutro]
    exact hn
  have hd : (n * g⁻¹) ∈ ClaseDcha N (g⁻¹) := by
    rw [hN (g⁻¹)];
    exact hi
  dsimp [ClaseDcha, RelDcha] at hd
  rw [Grupo.inv_inv] at hd
  have h_alg : g * (n * g⁻¹) = (g * n) * g⁻¹ := by rw [Grupo.oper_asociativa]
  rw [h_alg] at hd
  exact hd


/--  HK es subgrupo de G -/
def SubgrupoHK {G} [Grupo G] (H K : Subgrupo G) (h_forma : FormaSubgrupo (ProdConjuntos H K)) : Subgrupo G where
  filtro := ProdConjuntos H K
  neutro_sub := h_forma.1
  oper_sub hx hy := h_forma.2.1 _ _ hx hy
  inv_sub hx := h_forma.2.2 _ hx


/- Si H ⊲ G y K ⊲ G ⇒ HK ⊲ G -/
theorem prod_normal_es_normal {G} [Grupo G] (H K : Subgrupo G) (hH : H ⊲ G) (hK : K ⊲ G) :
    SubgrupoHK H K (corolario_hk_igual_kh H K hK) ⊲ G := by
  intro a
  ext b
  constructor
  · -- b ∈ a(HK) ⟹ b ∈ (HK)a
    intro hd
    dsimp [ClaseDcha, RelDcha, SubgrupoHK, ProdConjuntos] at hd
    rcases hd with ⟨h, k, hh, hk, hab⟩
    dsimp [ClaseIzq, RelIzq, SubgrupoHK, ProdConjuntos]
    use ((a * h) * a⁻¹), ((a * k) * a⁻¹)
    refine ⟨conj_normal H hH h a hh, conj_normal K hK k a hk, ?_⟩
    have h_b : b = a * (h * k) := by
      calc b = 1 * b := by rw [Grupo.neutro_oper b]
           _ = (a * a⁻¹) * b := by rw [← Grupo.inv_oper a]
           _ = a * (a⁻¹ * b) := by rw [Grupo.oper_asociativa]
           _ = a * (h * k) := by rw [hab]
    rw [h_b]
    calc (a * (h * k)) * a⁻¹
      _ = ((a * h) * k) * a⁻¹ := by rw [Grupo.oper_asociativa a h k]
      _ = ((a * h) * (1 * k)) * a⁻¹ := by rw [Grupo.neutro_oper k]
      _ = ((a * h) * ((a⁻¹ * a) * k)) * a⁻¹ := by rw [← Grupo.oper_inv a]
      _ = ((a * h) * (a⁻¹ * (a * k))) * a⁻¹ := by rw [← Grupo.oper_asociativa a⁻¹ a k]
      _ = (((a * h) * a⁻¹) * (a * k)) * a⁻¹ := by rw [Grupo.oper_asociativa (a * h) a⁻¹ (a * k)]
      _ = ((a * h) * a⁻¹) * ((a * k) * a⁻¹) := by rw [← Grupo.oper_asociativa ((a * h) * a⁻¹) (a * k) a⁻¹]

  · -- b ∈ (HK)a ⟹ b ∈ a(HK)
    intro hi
    dsimp [ClaseIzq, RelIzq, SubgrupoHK, ProdConjuntos] at hi
    rcases hi with ⟨h, k, hh, hk, hab⟩
    dsimp [ClaseDcha, RelDcha, SubgrupoHK, ProdConjuntos]
    use ((a⁻¹ * h) * (a⁻¹)⁻¹), ((a⁻¹ * k) * (a⁻¹)⁻¹)
    refine ⟨conj_normal H hH h a⁻¹ hh, conj_normal K hK k a⁻¹ hk, ?_⟩
    have h_b : b = (h * k) * a := by
      calc b = b * 1 := by rw [Grupo.oper_neutro b]
           _ = b * (a⁻¹ * a) := by rw [← Grupo.oper_inv a]
           _ = (b * a⁻¹) * a := by rw [← Grupo.oper_asociativa]
           _ = (h * k) * a := by rw [hab]
    rw [h_b]
    calc a⁻¹ * ((h * k) * a)
      _ = (a⁻¹ * (h * k)) * a := by rw [Grupo.oper_asociativa a⁻¹ (h * k) a]
      _ = ((a⁻¹ * h) * k) * a := by rw [Grupo.oper_asociativa a⁻¹ h k]
      _ = ((a⁻¹ * h) * (1 * k)) * a := by rw [Grupo.neutro_oper k]
      _ = ((a⁻¹ * h) * ((a * a⁻¹) * k)) * a := by rw [← Grupo.inv_oper a]
      _ = ((a⁻¹ * h) * (a * (a⁻¹ * k))) * a := by rw [← Grupo.oper_asociativa a a⁻¹ k]
      _ = (((a⁻¹ * h) * a) * (a⁻¹ * k)) * a := by rw [Grupo.oper_asociativa (a⁻¹ * h) a (a⁻¹ * k)]
      _ = ((a⁻¹ * h) * a) * ((a⁻¹ * k) * a) := by rw [← Grupo.oper_asociativa ((a⁻¹ * h) * a) (a⁻¹ * k) a]
      _ = ((a⁻¹ * h) * (a⁻¹)⁻¹) * ((a⁻¹ * k) * (a⁻¹)⁻¹) := by rw [Grupo.inv_inv a]




/- Ahora tratamos el grupo cociente G/K -/
-- La multiplicación está bien definida
theorem mul_bien_definida {G} [Grupo G] (K : Subgrupo G) (h_norm : K ⊲ G) {a a' : G} (ha : RelDcha K a a') {b b' : G} (hb : RelDcha K b b') : RelDcha K (a * b) (a' * b') := by
  have hi : ((a⁻¹ * a') * b) ∈ ClaseIzq K b := by
    dsimp [ClaseIzq, RelIzq]
    rw [← Grupo.oper_asociativa, Grupo.inv_oper, Grupo.oper_neutro]
    exact ha
  have hd : ((a⁻¹ * a') * b) ∈ ClaseDcha K b := by
   rw [h_norm b]
   exact hi
  dsimp [ClaseDcha, RelDcha] at hd
  have h_prod := K.oper_sub hd hb
  have h_final : (b⁻¹ * ((a⁻¹ * a') * b)) * (b⁻¹ * b') = ((a * b)⁻¹) * (a' * b') := by
    rw [Grupo.inv_compuesto, ← Grupo.oper_asociativa b⁻¹ ((a⁻¹ * a') * b) (b⁻¹ * b'), ← Grupo.oper_asociativa (a⁻¹ * a') b (b⁻¹ * b'), Grupo.oper_asociativa b b⁻¹ b', Grupo.inv_oper, Grupo.neutro_oper, ← Grupo.oper_asociativa a⁻¹ a' b', Grupo.oper_asociativa b⁻¹ a⁻¹ (a' * b')]
  dsimp [RelDcha]
  rw [← h_final]
  exact h_prod


-- El inverso está bien definido
theorem inv_bien_definido {G} [Grupo G] (K : Subgrupo G) (h_norm : K ⊲ G)
    {a a' : G} (ha : RelDcha K a a') :
    RelDcha K (a⁻¹) (a'⁻¹) := by
  have hk : K.filtro (a'⁻¹ * a) := by
    have h := K.inv_sub ha
    rw [Grupo.inv_compuesto, Grupo.inv_inv] at h
    exact h
  have hd : ((a * a'⁻¹) * a) ∈ ClaseDcha K a := by
    dsimp [ClaseDcha, RelDcha]
    rw [Grupo.oper_asociativa a⁻¹ (a * a'⁻¹) a,Grupo.oper_asociativa a⁻¹ a a'⁻¹, Grupo.oper_inv, Grupo.neutro_oper]
    exact hk
  have hi : ((a * a'⁻¹) * a) ∈ ClaseIzq K a := by
    rw [← h_norm a]
    exact hd
  dsimp [ClaseIzq, RelIzq] at hi
  have h_alg2 : ((a * a'⁻¹) * a) * a⁻¹ = a * a'⁻¹ := by
    rw [← Grupo.oper_asociativa (a * a'⁻¹) a a⁻¹, Grupo.inv_oper, Grupo.oper_neutro]
  dsimp [RelDcha]
  rw [Grupo.inv_inv, ← h_alg2]
  exact hi


-- El cociente forma un grupo
instance GrupoCociente {G} [Grupo G] (K : Subgrupo G) (h_norm : K ⊲ G) : Grupo (Quotient (setoidDcha K)) where

  -- Usamos 'intro' para evitar repetir las hipótesis de que a ~ a' y b ~ b' cada vez que queremos demostrar que la operación está bien definida
  -- Quotient.map₂ sirve para definir la multiplicación en el cociente a partir de la multiplicación en G
  mul := Quotient.map₂ (fun x y => x * y) (by intro a a' ha b b' hb; exact mul_bien_definida K h_norm ha hb)
  one := Quotient.mk (setoidDcha K) 1
  inv := Quotient.map (fun x => x⁻¹) (by intro a a' ha; exact inv_bien_definido K h_norm ha)

  oper_asociativa x y z := by
    -- Quotient.ind nos permite hacer inducción sobre las clases laterales
    --  congrArg sirve para aplicar la función que envía un elemento a su clase lateral a ambos lados de la igualdad
    induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
    exact congrArg (fun e => Quotient.mk (setoidDcha K) e) (Grupo.oper_asociativa _ _ _)

  oper_neutro x := by
    induction x using Quotient.ind
    exact congrArg (fun e => Quotient.mk (setoidDcha K) e) (Grupo.oper_neutro _)

  neutro_oper x := by
    induction x using Quotient.ind
    exact congrArg (fun e => Quotient.mk (setoidDcha K) e) (Grupo.neutro_oper _)

  oper_inv x := by
    induction x using Quotient.ind
    exact congrArg (fun e => Quotient.mk (setoidDcha K) e) (Grupo.oper_inv _)

  inv_oper x := by
    induction x using Quotient.ind
    exact congrArg (fun e => Quotient.mk (setoidDcha K) e) (Grupo.inv_oper _)


/- HOMOMORFISMO DE GRUPOS -/

-- Usamos variable para no tener que repetir las hipótesis de grupo cada vez
variable {G G' : Type _} [Grupo G] [Grupo G']

-- Definición de homomorfismo de grupos
def EsHomomorfismo (f : G → G') : Prop :=
  ∀ a b : G, f (a * b) = f a * f b

-- Homomorfismo preserva el elemento neutro
theorem hom_neutro (f : G → G') (hf : EsHomomorfismo f) : f 1 = 1 := by
  have h : f 1 * f 1 = f 1 * 1 := by
    calc f 1 * f 1 = f (1 * 1) := (hf 1 1).symm
      _ = f 1 := by rw [Grupo.oper_neutro]
      _ = f 1 * 1 := by rw [Grupo.oper_neutro]
  exact Grupo.oper_cancel_izq (f 1) 1 (f 1) h

-- Homomorfismo preserva el inverso
theorem hom_inv (f : G → G') (hf : EsHomomorfismo f) (a : G) : f (a⁻¹) = (f a)⁻¹ := by
  have h : f a * f (a⁻¹) = 1 := by
    rw [← hf a (a⁻¹), Grupo.inv_oper, hom_neutro f hf]
  exact Grupo.inv_unico (f a) (f (a⁻¹)) h


-- El núcleo (Ker) es un subgrupo de G
def Ker (f : G → G') (hf : EsHomomorfismo f) : Subgrupo G where
  filtro x := f x = 1
  neutro_sub := hom_neutro f hf
  oper_sub := by
    intro x y hx hy
    rw [hf x y, hx, hy, Grupo.oper_neutro]
  inv_sub := by
    intro x hx
    rw [hom_inv f hf x, hx, Grupo.inv_neutro]

-- La Imagen (Im) es un subgrupo de G'
def Im (f : G → G') (hf : EsHomomorfismo f) : Subgrupo G' where
  filtro y := ∃ x : G, f x = y
  neutro_sub := ⟨1, hom_neutro f hf⟩
  oper_sub := by
    intro y₁ y₂ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
    use (x₁ * x₂)
    rw [hf x₁ x₂, hx₁, hx₂]
  inv_sub := by
    intro y ⟨x, hx⟩
    use x⁻¹
    rw [hom_inv f hf x, hx]

-- Ker(f) ⊲ G
theorem ker_es_normal (f : G → G') (hf : EsHomomorfismo f) : Ker f hf ⊲ G := by
  intro a
  ext b
  dsimp [ClaseDcha, ClaseIzq, RelDcha, RelIzq, Ker]
  constructor
  · -- aH ⊆ Ha
    intro hd
    have h1 : (f a)⁻¹ * f b = 1 := by rw [← hom_inv f hf, ← hf, hd]
    have h2 : f b = f a := by
      calc f b = 1 * f b := by rw [Grupo.neutro_oper]
           _ = (f a * (f a)⁻¹) * f b := by rw [← Grupo.inv_oper]
           _ = f a * ((f a)⁻¹ * f b) := by rw [Grupo.oper_asociativa]
           _ = f a * 1 := by rw [h1]
           _ = f a := by rw [Grupo.oper_neutro]
    -- Añadimos hom_inv para transformar f(a⁻¹) en (f a)⁻¹
    rw [hf, hom_inv f hf, h2, Grupo.inv_oper]

  · -- Ha ⊆ aH
    intro hi
    have h1 : f b * (f a)⁻¹ = 1 := by rw [← hom_inv f hf, ← hf, hi]
    have h2 : f b = f a := by
      calc f b = f b * 1 := by rw [Grupo.oper_neutro]
           _ = f b * ((f a)⁻¹ * f a) := by rw [← Grupo.oper_inv]
           _ = (f b * (f a)⁻¹) * f a := by rw [← Grupo.oper_asociativa]
           _ = 1 * f a := by rw [h1]
           _ = f a := by rw [Grupo.neutro_oper]
    -- Lo mismo aquí con hom_inv y oper_inv
    rw [hf, hom_inv f hf, h2, Grupo.oper_inv]


-- Homomorfismo Inyectivo
def HomInyectivo (f : G → G') : Prop :=
  ∀ a b : G, f a = f b → a = b

-- Homomorfismo Sobreyectivo
def HomSobreyectivo (f : G → G') : Prop :=
  ∀ y : G', ∃ x : G, f x = y


-- Isomorfismo: Es homomorfismo, inyectivo y sobreyectivo
def EsIsomorfismo (f : G → G') : Prop :=
  EsHomomorfismo f ∧ HomInyectivo f ∧ HomSobreyectivo f

-- G y G' son isomorfos
def SonIsomorfos (G G' : Type _) [Grupo G] [Grupo G'] : Prop :=
  ∃ f : G → G', EsIsomorfismo f

-- Notación para G ≈ G'
notation G " ≈ " G' => SonIsomorfos G G'


-- Dos subgrupos son iguales si contienen exactamente los mismos elementos
theorem subgrupo_igualdad {G} [Grupo G] (H K : Subgrupo G) (h : ∀ x, H.filtro x ↔ K.filtro x) : H = K := by
  -- Extraemos las partes de las estructuras de subgrupo para poder usar la hipótesis de que contienen los mismos elementos
  obtain ⟨fH, nH, oH, iH⟩ := H
  obtain ⟨fK, nK, oK, iK⟩ := K
  -- Demostramos que las funciones filtro son la misma
  have heq : fH = fK := funext (fun x => propext (h x))
  cases heq
  rfl

-- f es inyectivo ↔ Ker f = {1}
theorem hom_inyectivo_ker_triv {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) : HomInyectivo f ↔ Ker f hf = SubgrupoTrivial G := by
  constructor
  · -- ⇒ Si f es inyectiva, Ker f = {1}
    intro h_iny
    apply subgrupo_igualdad
    intro x
    dsimp [Ker, SubgrupoTrivial]
    constructor
    · intro hx
      -- Si f(x) = 1, como f(1) = 1, entonces f(x) = f(1)
      have h_eq : f x = f 1 := by
        calc f x = 1 := hx
             _ = f 1 := (hom_neutro f hf).symm
      -- Por la inyectividad, entonces x = 1
      exact h_iny x 1 h_eq
    · intro hx
      -- Si x = 1, evaluamos f(1) que sabemos que es 1
      rw [hx]
      exact hom_neutro f hf

  · -- ⇐ Si Ker f = {1}, f es inyectiva
    intro h_ker a b hab
    -- f(a) = f(b) y multiplicamos por f(b)⁻¹ a la derecha
    have h1 : f a * (f b)⁻¹ = f b * (f b)⁻¹ := by rw [hab]
    rw [Grupo.inv_oper] at h1
    -- f(b)⁻¹ = f(b⁻¹)
    rw [← hom_inv f hf b] at h1
    -- f(a)*f(b⁻¹) = f(ab⁻¹)
    rw [← hf a (b⁻¹)] at h1
    have h_in_ker : (Ker f hf).filtro (a * b⁻¹) := h1
    -- Como Ker f es trivial, eontonces ab⁻¹ = 1
    rw [h_ker] at h_in_ker
    dsimp [SubgrupoTrivial] at h_in_ker
    calc a = a * 1 := by rw [Grupo.oper_neutro]
         _ = a * (b⁻¹ * b) := by rw [← Grupo.oper_inv b]
         _ = (a * b⁻¹) * b := by rw [Grupo.oper_asociativa]
         _ = 1 * b := by rw [h_in_ker]
         _ = b := by rw [Grupo.neutro_oper]


-- homomorfismo no nulo (su núcleo no es todo G)
def HomNoNulo {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) : Prop :=
  Ker f hf ≠ SubgrupoTotal G

-- Si G es simple, todo homomorfismo no nulo es inyectivo.
theorem hom_inyectivo_de_grupo_simple {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) (h_simple : ∀ H : Subgrupo G, (H ⊲ G) → H = SubgrupoTrivial G ∨ H = SubgrupoTotal G) (h_no_nulo : HomNoNulo f hf) : HomInyectivo f := by
  rw [hom_inyectivo_ker_triv f hf]
  have h_norm := ker_es_normal f hf
  -- Por ser G simple, el núcleo solo puede ser {1} o G
  have h_opciones := h_simple (Ker f hf) h_norm
  -- Como f no es nulo, el núcleo no es G. Por descarte, es {1}.
  cases h_opciones with
  | inl h_trivial => exact h_trivial
  | inr h_total => contradiction


-- creamos una instancia local para que Lean reconozca que G/Ker(f) es un Grupo.
local instance GrupoCocienteKer {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) :
  Grupo (Quotient (setoidDcha (Ker f hf))) := GrupoCociente (Ker f hf) (ker_es_normal f hf)

-- Definimos la función inducida f_barra : G/Ker(f) → Im(f)
-- Usamos Quotient.lift para demostrar que si a ~ b, entonces f(a) = f(b)
def f_barra {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) :
    Quotient (setoidDcha (Ker f hf)) → {y : G' // (Im f hf).filtro y} :=
  Quotient.lift (fun x => ⟨f x, ⟨x, rfl⟩⟩) (by
    intro a b hab
    apply Subtype.ext
    dsimp [setoidDcha, RelDcha, Ker] at hab
    have h1 : f (a⁻¹ * b) = 1 := hab
    rw [hf (a⁻¹) b, hom_inv f hf a] at h1
    -- Despejamos f(b) = f(a)
    symm
    calc f b = 1 * f b := by rw [Grupo.neutro_oper]
         _ = (f a * (f a)⁻¹) * f b := by rw [← Grupo.inv_oper (f a)]
         _ = f a * ((f a)⁻¹ * f b) := by rw [Grupo.oper_asociativa]
         _ = f a * 1 := by rw [h1]
         _ = f a := by rw [Grupo.oper_neutro]
  )

-- f_barra es un Isomorfismo (1er teorema de isomorfia)
theorem primer_teorema_isomorfia {G G'} [Grupo G] [Grupo G'] (f : G → G') (hf : EsHomomorfismo f) : EsIsomorfismo (f_barra f hf) := by
  refine ⟨?_, ?_, ?_⟩
  · -- es Homomorfismo: f_barra(a * b) = f_barra(a) * f_barra(b)
    -- usamos Quotient.ind para hacer inducción sobre las clases laterales
    apply Quotient.ind₂
    intro a b
    apply Subtype.ext
    dsimp [f_barra]
    exact hf a b

  · -- es inyectivo: f_barra(a) = f_barra(b) ⟹ a = b
    apply Quotient.ind₂
    intro a b h_eq
    have h_eq_val : f a = f b := congrArg Subtype.val h_eq
    -- Queremos ver que a ~ b, es decir (a⁻¹ * b) ∈ Ker(f)
    -- Usamos Quotient.sound para demostrar que a ~ b a partir de la igualdad de sus imágenes
    apply Quotient.sound
    change f (a⁻¹ * b) = 1
    rw [hf (a⁻¹) b, hom_inv f hf a]
    -- Sustituimos f(a) por f(b) para obtener (f b)⁻¹ * f b = 1
    rw [h_eq_val, Grupo.oper_inv]
  · -- es Sobreyectivo: ∀ y ∈ Im(f), ∃ x ∈ G/Ker(f) tal que f_barra(x) = y
    intro ⟨y, hy⟩
    -- hy dice que existe un x en G tal que f(x) = y
    rcases hy with ⟨x, hx⟩
    use Quotient.mk (setoidDcha (Ker f hf)) x
    apply Subtype.ext
    dsimp [f_barra]
    exact hx




-- ACCIOM DE UN GRUPO SOBRE UN CONJUNTO --


-- Definición de Acción de Grupo
class AccionGrupo (G : Type _) (X : Type _) [Grupo G] where
  -- ρ : G × X → X
  rho : G → X → X
  -- ρ(e, x) = x
  accion_neutro : ∀ x : X, rho 1 x = x
  --  ρ(g', ρ(g, x)) = ρ(g'g, x)
  -- lo escribimos como ρ(g1 * g2, x) = ρ(g1, ρ(g2, x))
  accion_comp : ∀ g1 g2 : G, ∀ x : X, rho (g1 * g2) x = rho g1 (rho g2 x)


namespace AccionGrupo

-- Fijamos G y X para no tener que escribirlos en cada definición
variable {G X : Type _} [Grupo G] [AccionGrupo G X]


-- Elementos de X que permanecen fijos bajo toda la acción (X₀)
def PuntosFijos : X → Prop :=
  fun x => ∀ g : G, rho g x = x


-- Órbita de un elemento x (Oₓ)
def Orbita (x : X) : X → Prop :=
  fun y => ∃ g : G, y = rho g x


-- El Estabilizador de x (I(x)) y la demostración de que es un Subgrupo de G
def Estabilizador (x : X) : Subgrupo G where
  filtro g := rho g x = x
  neutro_sub := accion_neutro x
  oper_sub := by
    intro g1 g2 h1 h2
    calc rho (g1 * g2) x = rho g1 (rho g2 x) := accion_comp g1 g2 x
         _ = rho g1 x := by rw [h2]
         _ = x := by rw [h1]
  inv_sub := by
    intro g hg
    calc rho (g⁻¹) x = rho (g⁻¹) (rho g x) := by rw [hg]
         _ = rho (g⁻¹ * g) x := (accion_comp (g⁻¹) g x).symm
         _ = rho (1:G) x := by rw [Grupo.oper_inv g]
         _ = x := accion_neutro x

-- Cada g ∈ G define una biyección en X
def rho_biyeccion (g : G) : X ≃ X where
  toFun x := rho g x
  invFun x := rho (g⁻¹) x
  left_inv x := by
    dsimp
    calc rho (g⁻¹) (rho g x) = rho (g⁻¹ * g) x := (accion_comp (g⁻¹) g x).symm
         _ = rho (1:G) x := by rw [Grupo.oper_inv g]
         _ = x := accion_neutro x
  right_inv x := by
    dsimp
    calc rho g (rho (g⁻¹) x) = rho (g * g⁻¹) x := (accion_comp g (g⁻¹) x).symm
         _ = rho (1:G) x := by rw [Grupo.inv_oper g]
         _ = x := accion_neutro x


-- Definimos f : G/I(x) → O_x
def f_orbita (x : X) : Quotient (setoidDcha (Estabilizador (G := G) x)) → {y : X // Orbita (G := G) x y} :=
  -- Usamos Quotient.lift para definir la función a partir de una función en G,
  -- y demostramos que si a ~ b, entonces rho a x = rho b x
  Quotient.lift (fun g => ⟨rho g x, ⟨g, rfl⟩⟩) (by
    intro a b hab
    apply Subtype.ext
    dsimp
    have h1 : rho (a⁻¹ * b) x = x := hab
    calc rho a x = rho a (rho (a⁻¹ * b) x) := by rw [h1]
         _ = rho (a * (a⁻¹ * b)) x := (accion_comp a (a⁻¹ * b) x).symm
         _ = rho ((a * a⁻¹) * b) x := by rw [← Grupo.oper_asociativa]
         _ = rho (1 * b) x := by rw [Grupo.inv_oper a]
         _ = rho b x := by rw [Grupo.neutro_oper b]
  )


-- f es inyectiva
theorem f_orbita_inyectiva (x : X) : Function.Injective (f_orbita (G := G) x) := by
  -- Quotient.ind₂ nos permite hacer inducción sobre las clases laterales para 2 elementos a y b
  apply Quotient.ind₂
  intro a b h_eq
  have h_eq_val : rho a x = rho b x := congrArg Subtype.val h_eq
  -- Usamos Quotient.sound para demostrar que a ~ b, es decir, que (a⁻¹ * b) ∈ I(x)
  apply Quotient.sound
  change rho (a⁻¹ * b) x = x
  calc rho (a⁻¹ * b) x = rho a⁻¹ (rho b x) := accion_comp a⁻¹ b x
       _ = rho a⁻¹ (rho a x) := by rw [← h_eq_val]
       _ = rho (a⁻¹ * a) x := (accion_comp a⁻¹ a x).symm
       _ = rho (1:G) x := by rw [Grupo.oper_inv a]
       _ = x := accion_neutro x


-- Demostramos que f es sobreyectiva
theorem f_orbita_sobreyectiva (x : X) : Function.Surjective (f_orbita (G := G) x) := by
  intro ⟨y, hy⟩
  rcases hy with ⟨g, hg⟩
  use Quotient.mk (setoidDcha (Estabilizador (G := G) x)) g
  apply Subtype.ext
  dsimp [f_orbita]
  exact hg.symm


-- Hay entonces una biyección entrre G/I(x) y O_x
noncomputable def equiv_orbita_estabilizador (x : X) : Quotient (setoidDcha (Estabilizador (G := G) x)) ≃ {y : X // Orbita (G := G) x y} :=
  -- Le pasamos la funcion f_orbita y las pruebas de que es inyectiva y sobreyectiva para construir la biyección
  Equiv.ofBijective (f_orbita (G := G) x) ⟨f_orbita_inyectiva (G := G) x, f_orbita_sobreyectiva (G := G) x⟩



-- |O_x| = [G : I(x)]
theorem card_orb_eq_estabilizador [Fintype G] (x : X) [Fintype {y : X // Orbita (G := G) x y}] : Fintype.card {y : X // Orbita (G := G) x y} = [G : Estabilizador (G := G) x] := by
  unfold indice
  rw [card_num_clases_igual (Estabilizador (G := G) x)]
  exact Fintype.card_congr (equiv_orbita_estabilizador (G := G) x).symm




-- Definimos la relación de estar en la misma órbita: x ~ y si existe g tal que y = g*x
def RelOrbita (x y : X) : Prop :=
  ∃ g : G, y = rho g x

-- Demostramos que es una relación de equivalencia (Reflexiva, Simétrica y Transitiva)
theorem relOrbita_es_equivalencia : Equivalence (RelOrbita (G := G) (X := X)) := {
  refl := by
    intro x
    -- x = 1 * x
    use (1 : G)
    exact (accion_neutro x).symm

  symm := by
    intro x y ⟨g, hg⟩
    -- Si y = g * x, entonces x = g⁻¹ * y
    use g⁻¹
    calc x = rho (1 : G) x := (accion_neutro x).symm
         _ = rho (g⁻¹ * g) x := by rw [← Grupo.oper_inv g]
         _ = rho g⁻¹ (rho g x) := accion_comp g⁻¹ g x
         _ = rho g⁻¹ y := by rw [hg]

  trans := by
    intro x y z ⟨g1, h1⟩ ⟨g2, h2⟩
    -- Si y = g1 * x  y  z = g2 * y, entonces z = (g2 * g1) * x
    use (g2 * g1)
    calc z = rho g2 y := h2
         _ = rho g2 (rho g1 x) := by rw [h1]
         _ = rho (g2 * g1) x := (accion_comp g2 g1 x).symm
}

-- Definimos el  conjunto cociente X/G
def setoidOrbita : Setoid X :=
  ⟨RelOrbita (G := G), relOrbita_es_equivalencia⟩


open scoped BigOperators -- Esto es para usar el símbolo ∑


-- La ecuación de Órbitas.
-- El cardinal de X es igual a la suma de los cardinales de sus órbitas.
theorem ecuacion_orbitas [Fintype X] [Fintype G] [Fintype (Quotient (setoidOrbita (G := G) (X := X)))] :
    Fintype.card X = ∑ O : Quotient (setoidOrbita (G := G) (X := X)),
      Quotient.liftOn O (fun x => Fintype.card {y // Orbita (G := G) x y}) (by
        intro a b hab
        dsimp
        -- Construimos una biyección entre la órbita de 'a' y la órbita de 'b'
        apply Fintype.card_congr
        exact {
          toFun := fun ⟨y, hy⟩ => ⟨y, by
            rcases hy with ⟨g, hg⟩
            rcases hab with ⟨g_ab, h_ab⟩
            -- Demostramos que a = rho g_ab⁻¹ b
            have ha : a = rho (g_ab⁻¹) b := by
              calc a = rho (1 : G) a := (accion_neutro a).symm
                   _ = rho (g_ab⁻¹ * g_ab) a := by rw [← Grupo.oper_inv g_ab]
                   _ = rho g_ab⁻¹ (rho g_ab a) := accion_comp g_ab⁻¹ g_ab a
                   _ = rho g_ab⁻¹ b := by rw [← h_ab]
            -- Con esto, vemos que y está en la órbita de b
            use g * g_ab⁻¹
            calc y = rho g a := hg
                 _ = rho g (rho g_ab⁻¹ b) := by rw [ha]
                 _ = rho (g * g_ab⁻¹) b := (accion_comp g g_ab⁻¹ b).symm
          ⟩,
          invFun := fun ⟨y, hy⟩ => ⟨y, by
            rcases hy with ⟨g, hg⟩
            rcases hab with ⟨g_ab, h_ab⟩
            -- La dirección inversa es directa
            use g * g_ab
            calc y = rho g b := hg
                 _ = rho g (rho g_ab a) := by rw [h_ab]
                 _ = rho (g * g_ab) a := (accion_comp g g_ab a).symm
          ⟩,
          left_inv := fun _ => Subtype.ext rfl,
          right_inv := fun _ => Subtype.ext rfl
        }
      ) := by
  -- Añadimos la táctica classical para que Lean asuma que todo subconjunto es finito
  classical

  -- X es biyectivo a la unión disjunta de sus clases de equivalencia
  have e : X ≃ Σ O : Quotient (setoidOrbita (G := G) (X := X)), {y : X // Quotient.mk (setoidOrbita (G := G) (X := X)) y = O} :=
    (Equiv.sigmaFiberEquiv (Quotient.mk (setoidOrbita (G := G) (X := X)))).symm

  -- Por tanto, el cardinal de X es igual al cardinal de esta unión disjunta.
  rw [Fintype.card_congr e]
  --  El cardinal de una unión disjunta es la suma de los cardinales de cada una de sus partes.
  rw [Fintype.card_sigma]

  -- Usamos Finset.sum_congr para decir que los términos dentro del sumatorio son iguales.
  apply Finset.sum_congr rfl
  intro O _

  -- Abrimos la clase de equivalencia O
  induction O using Quotient.ind

  --Nombramos a la variable extra a como 'a' y a la hipótesis extra como 'h'
  rename_i a h
  dsimp

  -- Demostramos que el conjunto {y // ⟦y⟧ = ⟦a⟧} tiene el mismo cardinal que {y // Orbita a y}
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨y, hy⟩ => ⟨y, by
      -- hy nos dice que ⟦y⟧ = ⟦a⟧, es decir, RelOrbita y a.
      -- Por simetría, obtenemos RelOrbita a y (que es la definición de Orbita a y)
      have h_rel : (setoidOrbita (G := G) (X := X)).r y a := Quotient.exact hy
      exact relOrbita_es_equivalencia.symm h_rel
    ⟩,
    invFun := fun ⟨y, hy⟩ => ⟨y, by
      -- Al revés: si tenemos Orbita a y (RelOrbita a y),
      -- por simetría es RelOrbita y a, luego ⟦y⟧ = ⟦a⟧
      have h_rel : (setoidOrbita (G := G) (X := X)).r y a := relOrbita_es_equivalencia.symm hy
      exact Quotient.sound h_rel
    ⟩,
    left_inv := fun _ => Subtype.ext rfl,
    right_inv := fun _ => Subtype.ext rfl
  }


theorem max_potencia_factorial_primo (p r : ℕ) (hp : Nat.Prime p) (hr_pos : r ≥ 1) (h_div : p ^ r ∣ Nat.factorial p) : r = 1 := by
  -- Por contradicción
  by_contra h_neq
  -- Si r >= 1 y r != 1, obligatoriamente r >= 2
  have hr_ge_2 : r ≥ 2 := by omega

  -- Si p^r divide a p!, y r >= 2, por transitividad p^2 divide a p!
  have h_div2 : p ^ 2 ∣ Nat.factorial p :=
    Nat.dvd_trans (Nat.pow_dvd_pow p hr_ge_2) h_div

  -- Analizamos los casos del primo p. Por ser primo, no puede ser 0.
  cases p with
  | zero =>
    exact (Nat.not_prime_zero hp).elim
  | succ k =>
    -- Expresamos p como (k+1). Reescribimos p^2 como (k+1)*(k+1)
    rw [pow_two] at h_div2

    -- La definición de (k+1)! es (k+1) * k!
    rw [Nat.factorial_succ] at h_div2

    -- Tenemos (k+1)*(k+1) ∣ (k+1) * k!. Cancelamos (k+1) a ambos lados.
    rw [Nat.mul_dvd_mul_iff_left (Nat.succ_pos k)] at h_div2

    -- Si un número primo divide a k!, debe ser <= k
    have h_le : k + 1 ≤ k := (Nat.Prime.dvd_factorial hp).mp h_div2
    -- Contradicción evidente: k + 1 no puede ser menor o igual a k
    omega



-- El núcleo de la acción de G sobre G/H por traslaciones
def nucleo_accion {G : Type _} [Grupo G] (H : Subgrupo G) : Subgrupo G where
  filtro k := ∀ a : G, H.filtro ((a⁻¹) * k * a)

  neutro_sub := by
    intro a
    have h_eq : (a⁻¹ * 1) * a = 1 := by
      calc (a⁻¹ * 1) * a = a⁻¹ * a := by rw [Grupo.oper_neutro]
                       _ = 1 := by rw [Grupo.oper_inv]
    rw [h_eq]
    exact H.neutro_sub

  oper_sub := by
    intro x y hx hy a
    have hx_a := hx a
    have hy_a := hy a
    have hxy_H := H.oper_sub hx_a hy_a
    have h_eq : ((a⁻¹ * x) * a) * ((a⁻¹ * y) * a) = (a⁻¹ * (x * y)) * a := by
      calc ((a⁻¹ * x) * a) * ((a⁻¹ * y) * a)
        _ = (((a⁻¹ * x) * a) * (a⁻¹ * y)) * a := by rw [← Grupo.oper_asociativa ((a⁻¹ * x) * a) (a⁻¹ * y) a]
        _ = ((a⁻¹ * x) * (a * (a⁻¹ * y))) * a := by rw [← Grupo.oper_asociativa (a⁻¹ * x) a (a⁻¹ * y)]
        _ = ((a⁻¹ * x) * ((a * a⁻¹) * y)) * a := by rw [← Grupo.oper_asociativa a a⁻¹ y]
        _ = ((a⁻¹ * x) * (1 * y)) * a := by rw [Grupo.inv_oper]
        _ = ((a⁻¹ * x) * y) * a := by rw [Grupo.neutro_oper]
        _ = (a⁻¹ * (x * y)) * a := by rw [Grupo.oper_asociativa]
    rw [h_eq] at hxy_H
    exact hxy_H

  inv_sub := by
    intro x hx a
    have hx_a := hx a
    have hinv_H := H.inv_sub hx_a
    have h_eq : (((a⁻¹ * x) * a)⁻¹) = (a⁻¹ * x⁻¹) * a := by
      calc (((a⁻¹ * x) * a)⁻¹)
        _ = a⁻¹ * (a⁻¹ * x)⁻¹ := by rw [Grupo.inv_compuesto]
        _ = a⁻¹ * (x⁻¹ * (a⁻¹)⁻¹) := by rw [Grupo.inv_compuesto]
        _ = a⁻¹ * (x⁻¹ * a) := by rw [Grupo.inv_inv]
        _ = (a⁻¹ * x⁻¹) * a := by rw [← Grupo.oper_asociativa]
    rw [h_eq] at hinv_H
    exact hinv_H


-- El núcleo de la acción siempre es un subgrupo normal de G
theorem nucleo_accion_es_normal {G : Type _} [Grupo G] (H : Subgrupo G) : nucleo_accion H ⊲ G := by
  intro g
  ext x
  dsimp [ClaseDcha, RelDcha, ClaseIzq, RelIzq, nucleo_accion]
  constructor
  · intro h_dcha a
    have h_hyp := h_dcha (g⁻¹ * a)
    have h_eq : (((g⁻¹ * a)⁻¹ * (g⁻¹ * x)) * (g⁻¹ * a)) = ((a⁻¹ * (x * g⁻¹)) * a) := by
      calc (((g⁻¹ * a)⁻¹ * (g⁻¹ * x)) * (g⁻¹ * a))
        _ = ((a⁻¹ * (g⁻¹)⁻¹) * (g⁻¹ * x)) * (g⁻¹ * a) := by rw [Grupo.inv_compuesto]
        _ = ((a⁻¹ * g) * (g⁻¹ * x)) * (g⁻¹ * a) := by rw [Grupo.inv_inv]
        _ = (a⁻¹ * (g * (g⁻¹ * x))) * (g⁻¹ * a) := by rw [Grupo.oper_asociativa a⁻¹ g (g⁻¹ * x)]
        _ = (a⁻¹ * ((g * g⁻¹) * x)) * (g⁻¹ * a) := by rw [← Grupo.oper_asociativa g g⁻¹ x]
        _ = (a⁻¹ * (1 * x)) * (g⁻¹ * a) := by rw [Grupo.inv_oper]
        _ = (a⁻¹ * x) * (g⁻¹ * a) := by rw [Grupo.neutro_oper]
        _ = ((a⁻¹ * x) * g⁻¹) * a := by rw [Grupo.oper_asociativa]
        _ = (a⁻¹ * (x * g⁻¹)) * a := by rw [← Grupo.oper_asociativa a⁻¹ x g⁻¹]
    rw [← h_eq]
    exact h_hyp
  · intro h_izq a
    have h_hyp := h_izq (g * a)
    have h_eq : (((g * a)⁻¹ * (x * g⁻¹)) * (g * a)) = ((a⁻¹ * (g⁻¹ * x)) * a) := by
      calc (((g * a)⁻¹ * (x * g⁻¹)) * (g * a))
        _ = ((a⁻¹ * g⁻¹) * (x * g⁻¹)) * (g * a) := by rw [Grupo.inv_compuesto]
        _ = (a⁻¹ * (g⁻¹ * (x * g⁻¹))) * (g * a) := by rw [Grupo.oper_asociativa a⁻¹ g⁻¹ (x * g⁻¹)]
        _ = (a⁻¹ * ((g⁻¹ * x) * g⁻¹)) * (g * a) := by rw [← Grupo.oper_asociativa g⁻¹ x g⁻¹]
        _ = ((a⁻¹ * (g⁻¹ * x)) * g⁻¹) * (g * a) := by rw [← Grupo.oper_asociativa a⁻¹ (g⁻¹ * x) g⁻¹]
        _ = (a⁻¹ * (g⁻¹ * x)) * (g⁻¹ * (g * a)) := by rw [Grupo.oper_asociativa (a⁻¹ *(g⁻¹ * x)) g⁻¹ (g * a)]
        _ = (a⁻¹ * (g⁻¹ * x)) * ((g⁻¹ * g) * a) := by rw [← Grupo.oper_asociativa g⁻¹ g a]
        _ = (a⁻¹ * (g⁻¹ * x)) * (1 * a) := by rw [Grupo.oper_inv]
        _ = (a⁻¹ * (g⁻¹ * x)) * a := by rw [Grupo.neutro_oper]
    rw [← h_eq]
    exact h_hyp

-- El núcleo de la acción está siempre contenido en H
theorem nucleo_accion_contenido {G : Type _} [Grupo G] (H : Subgrupo G) : SubgrupoContenido (nucleo_accion H) H := by
  intro k hk
  have hk_1 := hk 1
  have h_eq : ((1:G)⁻¹ * k) * 1 = k := by
    calc ((1:G)⁻¹ * k) * 1 = (1 * k) * 1 := by rw [Grupo.inv_neutro]
                         _ = k * 1 := by rw [Grupo.neutro_oper]
                         _ = k := by rw [Grupo.oper_neutro]
  rw [h_eq] at hk_1
  exact hk_1




-- Consideramos el grupo de permutaciones de Mathlib dentro de nuestra clase Grupo para poder usarlo
instance GrupoPerm {A : Type _} : Grupo (Equiv.Perm A) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  oper_asociativa f g h := mul_assoc f g h
  oper_neutro f := mul_one f
  neutro_oper f := one_mul f
  oper_inv f := inv_mul_cancel f
  inv_oper f := mul_inv_cancel f


/- Homomorfismo de G a el grupo simétrico de G/H -/
def phi_equiv {G : Type _} [Grupo G] (H : Subgrupo G) (g : G) : Equiv.Perm (Quotient (setoidDcha H)) where
  toFun := Quotient.lift (fun x => Quotient.mk (setoidDcha H) (g * x)) (by
    intro a b hab
    apply Quotient.sound
    change H.filtro ((g * a)⁻¹ * (g * b))
    have h1 : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by
      calc (g * a)⁻¹ * (g * b) = (a⁻¹ * g⁻¹) * (g * b) := by rw [Grupo.inv_compuesto]
        _ = a⁻¹ * (g⁻¹ * (g * b)) := by rw [← Grupo.oper_asociativa]
        _ = a⁻¹ * ((g⁻¹ * g) * b) := by rw [Grupo.oper_asociativa g⁻¹ g b]
        _ = a⁻¹ * (1 * b) := by rw [Grupo.oper_inv]
        _ = a⁻¹ * b := by rw [Grupo.neutro_oper]
    rw [h1]
    exact hab
  )
  invFun := Quotient.lift (fun x => Quotient.mk (setoidDcha H) (g⁻¹ * x)) (by
    intro a b hab
    apply Quotient.sound
    -- Hacemos lo mismo aquí para ver la expresión real
    change H.filtro ((g⁻¹ * a)⁻¹ * (g⁻¹ * b))
    have h1 : (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = a⁻¹ * b := by
      calc (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = (a⁻¹ * (g⁻¹)⁻¹) * (g⁻¹ * b) := by rw [Grupo.inv_compuesto]
        _ = (a⁻¹ * g) * (g⁻¹ * b) := by rw [Grupo.inv_inv]
        _ = a⁻¹ * (g * (g⁻¹ * b)) := by rw [← Grupo.oper_asociativa]
        _ = a⁻¹ * ((g * g⁻¹) * b) := by rw [Grupo.oper_asociativa g g⁻¹ b]
        _ = a⁻¹ * (1 * b) := by rw [Grupo.inv_oper]
        _ = a⁻¹ * b := by rw [Grupo.neutro_oper]
    rw [h1]
    exact hab
  )
  left_inv := by
    intro q
    induction q using Quotient.ind
    rename_i x
    change Quotient.mk (setoidDcha H) (g⁻¹ * (g * x)) = Quotient.mk (setoidDcha H) x
    have h1 : (g⁻¹ * (g * x)) = x := by
      calc g⁻¹ * (g * x) = (g⁻¹ * g) * x := by rw [Grupo.oper_asociativa g⁻¹ g x]
        _ = 1 * x := by rw [Grupo.oper_inv]
        _ = x := by rw [Grupo.neutro_oper]
    rw [h1]
  right_inv := by
    intro q
    induction q using Quotient.ind
    rename_i x
    change Quotient.mk (setoidDcha H) (g * (g⁻¹ * x)) = Quotient.mk (setoidDcha H) x
    have h1 : (g * (g⁻¹ * x)) = x := by
      calc g * (g⁻¹ * x) = (g * g⁻¹) * x := by rw [Grupo.oper_asociativa g g⁻¹ x]
        _ = 1 * x := by rw [Grupo.inv_oper]
        _ = x := by rw [Grupo.neutro_oper]
    rw [h1]



-- Vemos que phi_equiv es un homomorfismo
theorem phi_equiv_es_homomorfismo {G : Type _} [Grupo G] (H : Subgrupo G) : EsHomomorfismo (phi_equiv H) := by
  intro a b
  apply Equiv.ext
  intro q
  induction q using Quotient.ind
  rename_i x
  -- Añadimos .symm para darle la vuelta a la igualdad de la asociatividad
  have h_eq : (a * b) * x = a * (b * x) := (Grupo.oper_asociativa a b x).symm
  exact Quotient.sound (by
    change H.filtro (((a * b) * x)⁻¹ * (a * (b * x)))
    -- Cambiamos inv_oper por oper_inv
    have h_inv : ((a * b) * x)⁻¹ * (a * (b * x)) = 1 := by rw [h_eq, Grupo.oper_inv]
    rw [h_inv]
    exact H.neutro_sub
  )

-- El núcleo de phi_equiv es exactamente el subgrupo K (nucleo_accion)
theorem ker_phi_eq_nucleo {G : Type _} [Grupo G] (H : Subgrupo G) : Ker (phi_equiv H) (phi_equiv_es_homomorfismo H) = nucleo_accion H := by
  apply subgrupo_igualdad
  intro k
  constructor
  · intro hk
    dsimp [Ker] at hk
    intro a
    have h1 := congrFun (congrArg Equiv.toFun hk) (Quotient.mk (setoidDcha H) a)
    dsimp [phi_equiv] at h1
    have h2 : (setoidDcha H).r a (k * a) := Quotient.exact h1.symm
    dsimp [setoidDcha, RelDcha] at h2
    rw [← Grupo.oper_asociativa]
    exact h2
  · intro hk
    dsimp [Ker]
    apply Equiv.ext
    intro q
    induction q using Quotient.ind
    rename_i a
    dsimp [phi_equiv]
    symm
    apply Quotient.sound
    change H.filtro (a⁻¹ * (k * a))
    rw [Grupo.oper_asociativa]
    exact hk a


theorem indice_primo_min_es_normal {G : Type _} [Grupo G] [Fintype G] (H : Subgrupo G) (p : ℕ) (hp_prime : Nat.Prime p) (h_indice : @indice G _ _ H = p)
 (hp_div : p ∣ orden_grupo G) (hp_min : ∀ q : ℕ, Nat.Prime q → q ∣ orden_grupo G → p ≤ q) : H ⊲ G := by

  have h_card_X : Fintype.card (Quotient (setoidIzq H)) = p := h_indice
  -- K es el núcleo de la acción
  let K : Subgrupo G := nucleo_accion H
  have hK_normal : K ⊲ G := nucleo_accion_es_normal H
  have hK_sub_H : SubgrupoContenido K H := nucleo_accion_contenido H

  -- Usamos el teorema de los índices
  have h_GK_eq : indice K = p * indice (res_sub K H) := by
    have h_ind := teorema_indices K H hK_sub_H
    rw [h_indice] at h_ind
    exact h_ind

  have h_p_div_GK : p ∣ indice K := by
    rw [h_GK_eq]
    exact Nat.dvd_mul_right p _

  -- G/K es isomorfo a un subgrupo del grupo simétrico S_X
  have h_GK_div_fact : indice K ∣ Nat.factorial p := by
    have phi_es_hom := phi_equiv_es_homomorfismo H
    have ker_eq_K := ker_phi_eq_nucleo H

    have iso := primer_teorema_isomorfia (phi_equiv H) phi_es_hom
    have h_bij : Function.Bijective (f_barra (phi_equiv H) phi_es_hom) := ⟨iso.2.1, iso.2.2⟩

    have card_ker_eq_im : Fintype.card (Quotient (setoidDcha (Ker (phi_equiv H) phi_es_hom))) = Fintype.card {y // (Im (phi_equiv H) phi_es_hom).filtro y} := by
      apply Fintype.card_congr
      exact Equiv.ofBijective _ h_bij

    have indice_K_eq_Im : indice K = Fintype.card {y // (Im (phi_equiv H) phi_es_hom).filtro y} := by
      calc indice K = Fintype.card (Quotient (setoidIzq K)) := rfl
        _ = Fintype.card (Quotient (setoidDcha K)) := card_num_clases_igual K
        _ = Fintype.card (Quotient (setoidDcha (Ker (phi_equiv H) phi_es_hom))) := by rw [ker_eq_K]
        _ = Fintype.card {y // (Im (phi_equiv H) phi_es_hom).filtro y} := card_ker_eq_im

    have lagrange_perm := lagrange (Im (phi_equiv H) phi_es_hom)
    have div_perm : Fintype.card {y // (Im (phi_equiv H) phi_es_hom).filtro y} ∣ orden_grupo (Equiv.Perm (Quotient (setoidDcha H))) := by
      exact ⟨[Equiv.Perm (Quotient (setoidDcha H)) : Im (phi_equiv H) phi_es_hom], lagrange_perm⟩

    have card_X : Fintype.card (Quotient (setoidDcha H)) = p := by
      rw [← card_num_clases_igual H]
      exact h_card_X

    have card_perm : orden_grupo (Equiv.Perm (Quotient (setoidDcha H))) = Nat.factorial p := by
      unfold orden_grupo
      rw [Fintype.card_perm, card_X]

    rw [indice_K_eq_Im, ← card_perm]
    exact div_perm

  -- Demostramos que p es el unico divisor primo de [G : K], luego [G:K] = p
  have h_solo_p_divide : ∀ q : ℕ, Nat.Prime q → q ∣ indice K → q = p := by
    intro q hq_prime hq_div
    have hq_le_p : q ≤ p := by
      have hq_div_fact : q ∣ Nat.factorial p := Nat.dvd_trans hq_div h_GK_div_fact
      exact (Nat.Prime.dvd_factorial hq_prime).mp hq_div_fact

    have hq_div_G : q ∣ orden_grupo G := by
      have h_GK_div_G : indice K ∣ orden_grupo G := by
        rw [lagrange K, Nat.mul_comm]
        exact Nat.dvd_mul_right (indice K) _
      exact Nat.dvd_trans hq_div h_GK_div_G

    have hp_le_q : p ≤ q := hp_min q hq_prime hq_div_G
    omega

  have h_GK_eq_p : indice K = p := by
    have ⟨m, hm⟩ := h_p_div_GK
    have h2 : p * m ∣ Nat.factorial p := by rw [← hm]; exact h_GK_div_fact
    cases p with
    | zero => exact (Nat.not_prime_zero hp_prime).elim
    | succ k =>
      have h_fact : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := rfl
      rw [h_fact] at h2
      have h3 : m ∣ Nat.factorial k := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
      have h_m_eq_1 : m = 1 := by
        by_contra h_m_neq_1
        have h_ex := Nat.exists_prime_and_dvd h_m_neq_1
        rcases h_ex with ⟨q, hq_prime, hq_div_m⟩
        have hq_div_kfact : q ∣ Nat.factorial k := Nat.dvd_trans hq_div_m h3
        have hq_le_k : q ≤ k := (Nat.Prime.dvd_factorial hq_prime).mp hq_div_kfact
        have hq_div_n : q ∣ indice K := by
          rw [hm]
          rcases hq_div_m with ⟨c, hc⟩
          use (k + 1) * c
          calc (k + 1) * m = (k + 1) * (q * c) := by rw [hc]
               _ = ((k + 1) * q) * c := by rw [← Nat.mul_assoc]
               _ = (q * (k + 1)) * c := by rw [Nat.mul_comm (k + 1) q]
               _ = q * ((k + 1) * c) := by rw [Nat.mul_assoc]
        have hq_eq_p : q = k + 1 := h_solo_p_divide q hq_prime hq_div_n
        rw [hq_eq_p] at hq_le_k
        omega
      rw [hm, h_m_eq_1, mul_one]


  -- Como [G : K] = p y [G : K] = p * [H : K], entonces queda que [H : K] = 1.
  have h_HK_eq_1 : indice (res_sub K H) = 1 := by
    have h_eq : p * 1 = p * indice (res_sub K H) := by
      calc p * 1 = p := mul_one p
           _ = indice K := h_GK_eq_p.symm
           _ = p * indice (res_sub K H) := h_GK_eq
    exact Nat.eq_of_mul_eq_mul_left hp_prime.pos h_eq.symm

  have h_H_eq_K : H = K := by
    apply subgrupo_igualdad
    intro x
    constructor
    · intro hx
      have h_subsing : Subsingleton (Quotient (setoidIzq (res_sub K H))) :=
        Fintype.card_le_one_iff_subsingleton.mp (by unfold indice at h_HK_eq_1; omega)
      let q_1 := Quotient.mk (setoidIzq (res_sub K H)) (1 : {y // H.filtro y})
      let q_x := Quotient.mk (setoidIzq (res_sub K H)) ⟨x, hx⟩
      have h_eq_q : q_1 = q_x := Subsingleton.elim q_1 q_x
      have h_rel : RelIzq (res_sub K H) (1 : {y // H.filtro y}) ⟨x, hx⟩ := Quotient.exact h_eq_q
      change K.filtro (x * (1:G)⁻¹) at h_rel
      have h_alg : x * (1:G)⁻¹ = x := by rw [Grupo.inv_neutro, Grupo.oper_neutro]
      rw [h_alg] at h_rel
      exact h_rel
    · intro hx
      exact hK_sub_H x hx

  -- Al ser H = K, y K normal, entonces H es normal.
  rw [h_H_eq_K]
  exact hK_normal



-- Ahora definimos lo que es un p-grupo
def EsPGrupo (G : Type _) [Grupo G] [Fintype G] (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m : ℕ, m > 0 ∧ orden_grupo G = p ^ m



-- Si p divide a cada elemento de un sumatorio, divide a la suma total
theorem p_divide_suma {α : Type _} (s : Finset α) (f : α → ℕ) (p : ℕ)
    (h : ∀ x ∈ s, p ∣ f x) : p ∣ ∑ x ∈ s, f x := by
  classical
  --Hacemos inducción sobre el conjunto finito s con Finset.induction_on
  induction s using Finset.induction_on with
  | empty =>
    -- La suma vacía es 0, y p | 0 siempre
    simp only [Finset.sum_empty]
    exact Nat.dvd_zero p
    -- En el caso inductivo usamos insert para separar un elemento 'a' del resto del conjunto s'
  | insert a s' ha ih =>
    -- Separamos la suma en 'a' y el resto del sumatorio '(s')'
    rw [Finset.sum_insert ha]
    apply Nat.dvd_add
    · -- Demostramos que p | f(a)
      apply h a
      --FInset.mem_insert_self a s' es la definición de que 'a' pertenece al conjunto
      exact Finset.mem_insert_self a s'
    · -- Demostramos por hipótesis de inducción que p | suma(s')
      apply ih
      intro x hx
      apply h x
      exact Finset.mem_insert_of_mem hx


theorem card_congr_puntos_fijos {G X : Type _} [Grupo G] [Fintype G] [AccionGrupo G X] [Fintype X] (p : ℕ) (h_pgrupo : EsPGrupo G p) [Fintype {x : X // PuntosFijos (G := G) x}]
    [Fintype (Quotient (setoidOrbita (G := G) (X := X)))] : Nat.ModEq p (Fintype.card X) (Fintype.card {x : X // PuntosFijos (G := G) x}) := by

  -- p es primo y |G| = p^m
  rcases h_pgrupo with ⟨hp, m, hm_pos, hG_card⟩
  -- Para no repetir el Quotient.liftOn varias veces definimos card_O
  let card_O (O : Quotient (setoidOrbita (G := G) (X := X))) : ℕ :=
    Quotient.liftOn O (fun x => Fintype.card {y // Orbita (G := G) x y}) (by
      intro a b hab
      apply Fintype.card_congr
      exact ⟨fun ⟨y, hy⟩ => ⟨y, relOrbita_es_equivalencia.trans (relOrbita_es_equivalencia.symm hab) hy⟩,
             fun ⟨y, hy⟩ => ⟨y, relOrbita_es_equivalencia.trans hab hy⟩,
             fun _ => Subtype.ext rfl,
             fun _ => Subtype.ext rfl⟩
    )

  -- Usamos la ecuación de orbitas
  have h_eq : Fintype.card X = ∑ O : Quotient (setoidOrbita (G := G) (X := X)), card_O O := by
    exact ecuacion_orbitas (G := G) (X := X)

  -- Separamos el sumatorio en órbitas triviales (tamaño 1) y no triviales (tamaño distinto de 1)
  have h_split : Fintype.card X =
      (∑ O ∈ Finset.univ.filter (fun O => card_O O = 1), card_O O) +
      (∑ O ∈ Finset.univ.filter (fun O => card_O O ≠ 1), card_O O) := by
    rw [h_eq]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun O => card_O O = 1) card_O).symm

  -- Demostramos que la suma de órbitas de tamaño 1 es exactamente el número de puntos fijos |X₀|
  have h_sum_fijos : ∑ O ∈ Finset.univ.filter (fun O => card_O O = 1), card_O O = Fintype.card {x : X // PuntosFijos (G := G) x} := by
    have h_unos : ∑ O ∈ Finset.univ.filter (fun O => card_O O = 1), card_O O = (Finset.univ.filter (fun O => card_O O = 1)).card := by
      calc ∑ O ∈ Finset.univ.filter (fun O => card_O O = 1), card_O O
        _ = ∑ O ∈ Finset.univ.filter (fun O => card_O O = 1), 1 := by
          apply Finset.sum_congr rfl
          intro O hO
          exact (Finset.mem_filter.mp hO).right
        _ = (Finset.univ.filter (fun O => card_O O = 1)).card := by simp

    rw [h_unos]

    let f : {O // card_O O = 1} ≃ {x : X // PuntosFijos (G := G) x} := {
      toFun := fun ⟨O, hO⟩ =>
        let x := O.out
        ⟨x, by
          intro g
          have h_orb_card : Fintype.card {y // Orbita (G := G) x y} = 1 := by
            have h_eq2 : Quotient.mk (setoidOrbita (G := G) (X := X)) x = O := Quotient.out_eq O
            rw [← h_eq2] at hO
            exact hO
          have h_orb_gx : Orbita (G := G) x (rho g x) := ⟨g, rfl⟩
          have h_sub : Subsingleton {y // Orbita (G := G) x y} := Fintype.card_le_one_iff_subsingleton.mp (by omega)
          have h_eq_y : (⟨rho g x, h_orb_gx⟩ : {y // Orbita (G := G) x y}) = ⟨x, ⟨1, (accion_neutro x).symm⟩⟩ := Subsingleton.elim _ _
          injection h_eq_y
        ⟩
      invFun := fun ⟨x, hx⟩ =>
        ⟨Quotient.mk (setoidOrbita (G := G) (X := X)) x, by
          dsimp [card_O]
          apply Fintype.card_eq_one_iff.mpr
          use ⟨x, ⟨1, (accion_neutro x).symm⟩⟩
          intro ⟨y, ⟨g, hg⟩⟩
          apply Subtype.ext
          dsimp
          rw [hg, hx g]
        ⟩
      left_inv := fun ⟨O, hO⟩ => Subtype.ext (Quotient.out_eq O)
      right_inv := fun ⟨x, hx⟩ => by
        ext
        dsimp
        have h_rel : RelOrbita (G := G) ((Quotient.mk (setoidOrbita (G := G) (X := X)) x).out) x :=
          Quotient.exact (Quotient.out_eq (Quotient.mk (setoidOrbita (G := G) (X := X)) x))
        rcases h_rel with ⟨g, hg⟩
        calc (Quotient.mk (setoidOrbita (G := G) (X := X)) x).out
          _ = rho 1 ((Quotient.mk (setoidOrbita (G := G) (X := X)) x).out) := (accion_neutro _).symm
          _ = rho (g⁻¹ * g) ((Quotient.mk (setoidOrbita (G := G) (X := X)) x).out) := by rw [← Grupo.oper_inv g]
          _ = rho g⁻¹ (rho g ((Quotient.mk (setoidOrbita (G := G) (X := X)) x).out)) := accion_comp _ _ _
          _ = rho g⁻¹ x := by rw [← hg]
          _ = x := hx g⁻¹
    }

    calc (Finset.univ.filter (fun O => card_O O = 1)).card
      _ = Fintype.card {O // card_O O = 1} := by rw [← Fintype.card_subtype]
      _ = Fintype.card {x : X // PuntosFijos (G := G) x} := Fintype.card_congr f

  -- Demostramos que las órbitas de tamaño > 1 son múltiplos de p
  have h_div_p : ∀ O ∈ Finset.univ.filter (fun O => card_O O ≠ 1), p ∣ card_O O := by
    intro O hO
    have h_neq_1 := (Finset.mem_filter.mp hO).right
    induction O using Quotient.ind
    rename_i x

    let n := Fintype.card {y // Orbita (G := G) x y}

    have h_n_neq_1 : n ≠ 1 := h_neq_1

    have h_div : n ∣ orden_grupo G := by
      change Fintype.card {y // Orbita (G := G) x y} ∣ orden_grupo G
      rw [card_orb_eq_estabilizador, lagrange (Estabilizador (G := G) x)]
      exact Nat.dvd_mul_left _ _

    have h_div_pm : n ∣ p^m := by
      rw [← hG_card]
      exact h_div

    have ⟨q, hq_prime, hq_div_n⟩ := Nat.exists_prime_and_dvd h_n_neq_1
    have hq_div_pm : q ∣ p^m := Nat.dvd_trans hq_div_n h_div_pm
    have hq_div_p : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq_prime hq_div_pm

    -- Usamos Nat.dvd_prime para evaluar los divisores de un primo
    have h_eq_or : q = 1 ∨ q = p := (Nat.dvd_prime hp).mp hq_div_p
    have hq_eq_p : q = p := by
      cases h_eq_or with
      | inl h1 =>
        have h_not_one : q ≠ 1 := Nat.Prime.ne_one hq_prime
        contradiction
      | inr hpq => exact hpq

    rw [← hq_eq_p]
    exact hq_div_n

  -- Usamos aritmética modular de suma divisoria
  have h_sum_mod : Nat.ModEq p (∑ O ∈ Finset.univ.filter (fun O => card_O O ≠ 1), card_O O) 0 := by
    apply Nat.modEq_zero_iff_dvd.mpr
    -- Usamos nuestro propio lema, y le pasamso el sumatorio, la función, el primo p y la hipótesis de antes
    exact p_divide_suma _ card_O p h_div_p

  -- |X| = |X0| + ∑|Ox| ≡ |X0| + 0 ≡ |X0| mod p
  rw [h_split, h_sum_fijos]
  have h_mod_add : Nat.ModEq p (Fintype.card {x : X // PuntosFijos (G := G) x} + ∑ O ∈ Finset.univ.filter (fun O => card_O O ≠ 1), card_O O) (Fintype.card {x : X // PuntosFijos (G := G) x} + 0) :=
    Nat.ModEq.add_left _ h_sum_mod

  rw [Nat.add_zero] at h_mod_add
  exact h_mod_add


 -- Definimos el Normalizador de H en G: N_G(H) = {g ∈ G | gHg⁻¹ = H}
def Normalizador {G : Type _} [Grupo G] (H : Subgrupo G) : Subgrupo G where
  filtro g := ∀ h : G, H.filtro h ↔ H.filtro ((g * h) * g⁻¹)
  neutro_sub := by
    intro h
    have h_eq : ((1:G) * h) * (1:G)⁻¹ = h := by
      calc ((1:G) * h) * (1:G)⁻¹
        _ = h * (1:G)⁻¹ := by rw [Grupo.neutro_oper]
        _ = h * 1 := by rw [Grupo.inv_neutro]
        _ = h := by rw [Grupo.oper_neutro]
    rw [h_eq]
  oper_sub := by
    intro x y hx hy h
    have h_eq : ((x * y) * h) * (x * y)⁻¹ = (x * ((y * h) * y⁻¹)) * x⁻¹ := by
      calc ((x * y) * h) * (x * y)⁻¹
        _ = ((x * y) * h) * (y⁻¹ * x⁻¹) := by rw [Grupo.inv_compuesto]
        _ = (x * (y * h)) * (y⁻¹ * x⁻¹) := by rw [Grupo.oper_asociativa x y h]
        _ = x * ((y * h) * (y⁻¹ * x⁻¹)) := by rw [Grupo.oper_asociativa x (y*h) (y⁻¹ * x⁻¹)]
        _ = x * (((y * h) * y⁻¹) * x⁻¹) := by rw [← Grupo.oper_asociativa (y * h) y⁻¹ x⁻¹]
        _ = (x * ((y * h) * y⁻¹)) * x⁻¹ := by rw [← Grupo.oper_asociativa x ((y * h) * y⁻¹) x⁻¹]
    rw [h_eq]
    -- Aplicamos la transitividad para demostrar que H.filtro ((x * y) * h) ↔ H.filtro ((x * ((y * h) * y⁻¹)) * x⁻¹)
    exact Iff.trans (hy h) (hx ((y * h) * y⁻¹))
  inv_sub := by
    intro x hx h
    have hx_eval := hx ((x⁻¹ * h) * (x⁻¹)⁻¹)
    have h_eq : (x * ((x⁻¹ * h) * (x⁻¹)⁻¹)) * x⁻¹ = h := by
      calc (x * ((x⁻¹ * h) * (x⁻¹)⁻¹)) * x⁻¹
        _ = (x * ((x⁻¹ * h) * x)) * x⁻¹ := by rw [Grupo.inv_inv]
        _ = ((x * (x⁻¹ * h)) * x) * x⁻¹ := by rw [← Grupo.oper_asociativa x (x⁻¹ * h) x]
        _ = (((x * x⁻¹) * h) * x) * x⁻¹ := by rw [← Grupo.oper_asociativa x x⁻¹ h]
        _ = ((1 * h) * x) * x⁻¹ := by rw [Grupo.inv_oper x]
        _ = (h * x) * x⁻¹ := by rw [Grupo.neutro_oper]
        _ = h * (x * x⁻¹) := by rw [Grupo.oper_asociativa]
        _ = h * 1 := by rw [Grupo.inv_oper x]
        _ = h := by rw [Grupo.oper_neutro]
    rw [h_eq] at hx_eval
    -- hx_eval ahora es  H.filtro ((x⁻¹ * h) * (x⁻¹)⁻¹) ↔ H.filtro h, pero lo necesitamos al revés
    exact hx_eval.symm



-- H ≤ N_G(H) (H less or equal (le) menor o igual que normalizdor)
theorem H_le_normalizador {G : Type _} [Grupo G] (H : Subgrupo G) : SubgrupoContenido H (Normalizador H) := by
  intro x hx h
  constructor
  · intro hh
    -- H.filtro h → H.filtro ((x * h) * x⁻¹)
    have h1 : H.filtro (x * h) := H.oper_sub hx hh
    have h2 : H.filtro (x⁻¹) := H.inv_sub hx
    exact H.oper_sub h1 h2
  · intro hh
    -- H.filtro ((x * h) * x⁻¹) → H.filtro h
    -- Multiplicamos por la izquierda por x⁻¹ y por la derecha por x
    have h1 : H.filtro (x⁻¹) := H.inv_sub hx
    have h3 : H.filtro (x⁻¹ * ((x * h) * x⁻¹)) := H.oper_sub h1 hh
    have h4 : H.filtro ((x⁻¹ * ((x * h) * x⁻¹)) * x) := H.oper_sub h3 hx
    have h_eq : (x⁻¹ * ((x * h) * x⁻¹)) * x = h := by
      calc (x⁻¹ * ((x * h) * x⁻¹)) * x
        _ = ((x⁻¹ * (x * h)) * x⁻¹) * x := by rw [← Grupo.oper_asociativa x⁻¹ (x * h) x⁻¹]
        _ = (((x⁻¹ * x) * h) * x⁻¹) * x := by rw [← Grupo.oper_asociativa x⁻¹ x h]
        _ = ((1 * h) * x⁻¹) * x := by rw [Grupo.oper_inv x]
        _ = (h * x⁻¹) * x := by rw [Grupo.neutro_oper]
        _ = h * (x⁻¹ * x) := by rw [Grupo.oper_asociativa]
        _ = h * 1 := by rw [Grupo.oper_inv x]
        _ = h := by rw [Grupo.oper_neutro]
    rw [h_eq] at h4
    exact h4


-- La acción de H sobre las clases laterales izquierdas X = G/H por traslación
instance accion_H_cociente {G : Type _} [Grupo G] (H : Subgrupo G) : AccionGrupo {x // H.filtro x} (Quotient (setoidDcha H)) where
  rho h q := Quotient.liftOn q
    (fun a => Quotient.mk (setoidDcha H) (h.val * a))
    (by
      intro a b hab
      apply Quotient.sound
      change H.filtro (((h.val * a)⁻¹) * (h.val * b))
      have h_calc : ((h.val * a)⁻¹) * (h.val * b) = a⁻¹ * b := by
        calc ((h.val * a)⁻¹) * (h.val * b)
          _ = (a⁻¹ * h.val⁻¹) * (h.val * b) := by rw [Grupo.inv_compuesto]
          _ = a⁻¹ * (h.val⁻¹ * (h.val * b)) := by rw [← Grupo.oper_asociativa]
          _ = a⁻¹ * ((h.val⁻¹ * h.val) * b) := by rw [Grupo.oper_asociativa h.val⁻¹ h.val b]
          _ = a⁻¹ * (1 * b) := by rw [Grupo.oper_inv]
          _ = a⁻¹ * b := by rw [Grupo.neutro_oper]

      rw [h_calc]
      exact hab
    )

  accion_neutro := by
    intro q
    induction q using Quotient.ind
    rename_i a -- Le damos un nombre a la variable que genera la inducción
    apply Quotient.sound
    change H.filtro ((1 * a)⁻¹ * a)
    have h_calc : (1 * a)⁻¹ * a = 1 := by
      calc (1 * a)⁻¹ * a = a⁻¹ * a := by rw [Grupo.neutro_oper]
           _ = 1 := by rw [Grupo.oper_inv]
    rw [h_calc]
    exact H.neutro_sub

  accion_comp := by
    intro h1 h2 q
    induction q using Quotient.ind
    rename_i a
    apply Quotient.sound
    change H.filtro (((h1.val * h2.val) * a)⁻¹ * (h1.val * (h2.val * a)))
    have h_calc : ((h1.val * h2.val) * a)⁻¹ * (h1.val * (h2.val * a)) = 1 := by
      calc ((h1.val * h2.val) * a)⁻¹ * (h1.val * (h2.val * a))
        _ = (a⁻¹ * (h1.val * h2.val)⁻¹) * (h1.val * (h2.val * a)) := by rw [Grupo.inv_compuesto]
        _ = (a⁻¹ * (h2.val⁻¹ * h1.val⁻¹)) * (h1.val * (h2.val * a)) := by rw [Grupo.inv_compuesto]
        _ = a⁻¹ * ((h2.val⁻¹ * h1.val⁻¹) * (h1.val * (h2.val * a))) := by rw [← Grupo.oper_asociativa]
        _ = a⁻¹ * (h2.val⁻¹ * (h1.val⁻¹ * (h1.val * (h2.val * a)))) := by rw [← Grupo.oper_asociativa]
        _ = a⁻¹ * (h2.val⁻¹ * ((h1.val⁻¹ * h1.val) * (h2.val * a))) := by rw [Grupo.oper_asociativa h1.val⁻¹ h1.val _]
        _ = a⁻¹ * (h2.val⁻¹ * (1 * (h2.val * a))) := by rw [Grupo.oper_inv]
        _ = a⁻¹ * (h2.val⁻¹ * (h2.val * a)) := by rw [Grupo.neutro_oper]
        _ = a⁻¹ * ((h2.val⁻¹ * h2.val) * a) := by rw [← Grupo.oper_asociativa]
        _ = a⁻¹ * (1 * a) := by rw [Grupo.oper_inv]
        _ = a⁻¹ * a := by rw [Grupo.neutro_oper]
        _ = 1 := by rw [Grupo.oper_inv]
    rw [h_calc]
    exact H.neutro_sub


-- [N_G(H) : H] ≡ [G : H] (mod p)
theorem indice_normalizador_congr_p {G : Type _} [Grupo G] [Fintype G] (p : ℕ) (H : Subgrupo G) (h_pgrupo : EsPGrupo {x // H.filtro x} p) :
    Fintype.card (Quotient (setoidDcha H)) ≡ Fintype.card {q : Quotient (setoidDcha H) // PuntosFijos (G := {x // H.filtro x}) q} [MOD p] := by
  -- Aplicamos card_congr_puntos_fijos directamente a la acción que acabamos de definir
  exact card_congr_puntos_fijos (G := {x // H.filtro x}) (X := Quotient (setoidDcha H)) p h_pgrupo


--Definimos el Centro de un grupo Z(G)
def Centro (G : Type _) [Grupo G] : Subgrupo G where
  filtro z := ∀ g : G, z * g = g * z

  neutro_sub := by
    intro g
    calc 1 * g = g := by rw [Grupo.neutro_oper]
         _ = g * 1 := by rw [Grupo.oper_neutro]

  oper_sub := by
    intro x y hx hy g
    calc (x * y) * g = x * (y * g) := by rw [← Grupo.oper_asociativa]
         _ = x * (g * y) := by rw [hy g]
         _ = (x * g) * y := by rw [Grupo.oper_asociativa]
         _ = (g * x) * y := by rw [hx g]
         _ = g * (x * y) := by rw [← Grupo.oper_asociativa]

  inv_sub := by
    intro x hx g
    -- Usamos el teorema conmutan_inv
    exact conmutan_inv (hx g)


-- Definimos la acción de G sobre sí mismo por conjugación ρ(g, x) = gxg⁻¹
local instance accion_conjugacion {G : Type _} [Grupo G] : AccionGrupo G G where
  rho g x := (g * x) * g⁻¹

  accion_neutro := by
    intro x
    calc (1 * x) * (1:G)⁻¹ = x * (1:G)⁻¹ := by rw [Grupo.neutro_oper]
         _ = x * 1 := by rw [Grupo.inv_neutro]
         _ = x := by rw [Grupo.oper_neutro]

  accion_comp := by
    intro g1 g2 x
    calc ((g1 * g2) * x) * (g1 * g2)⁻¹
      _ = ((g1 * g2) * x) * (g2⁻¹ * g1⁻¹) := by rw [Grupo.inv_compuesto]
      _ = (g1 * (g2 * x)) * (g2⁻¹ * g1⁻¹) := by rw [← Grupo.oper_asociativa g1 g2 x]
      _ = g1 * ((g2 * x) * (g2⁻¹ * g1⁻¹)) := by rw [← Grupo.oper_asociativa]
      _ = g1 * (((g2 * x) * g2⁻¹) * g1⁻¹) := by rw [Grupo.oper_asociativa (g2*x) g2⁻¹ g1⁻¹]
      _ = (g1 * ((g2 * x) * g2⁻¹)) * g1⁻¹ := by rw [Grupo.oper_asociativa]

-- Los elementos fijos bajo conjugación (X0) son exactamente Z(G)
theorem fijos_conjugacion_eq_centro {G : Type _} [Grupo G] (x : G) : PuntosFijos (G := G) (X := G) x ↔ (Centro G).filtro x := by
  -- gxg⁻¹ = x ↔ gx = xg
  constructor
  · intro h g
    have h1 := h g -- (g * x) * g⁻¹ = x
    change (g * x) * g⁻¹ = x at h1
    calc x * g = ((g * x) * g⁻¹) * g := by rw [h1]
         _ = (g * x) * (g⁻¹ * g) := by rw [← Grupo.oper_asociativa]
         _ = (g * x) * 1 := by rw [Grupo.oper_inv]
         _ = g * x := by rw [Grupo.oper_neutro]
  · intro h g
    have h1 := h g -- x * g = g * x
    calc (g * x) * g⁻¹ = (x * g) * g⁻¹ := by rw [h1]
         _ = x * (g * g⁻¹) := by rw [← Grupo.oper_asociativa]
         _ = x * 1 := by rw [Grupo.inv_oper]
         _ = x := by rw [Grupo.oper_neutro]




-- Si G es un p-grupo, |Z(G)| > 1
theorem centro_p_grupo_mayor_uno {G : Type _} [Grupo G] [Fintype G] (p : ℕ) (h_pgrupo : EsPGrupo G p) [Fintype {x : G // PuntosFijos (G := G) (X := G) x}]
  [Fintype (Quotient (setoidOrbita (G := G) (X := G)))] [Fintype {z : G // (Centro G).filtro z}] : Fintype.card {z : G // (Centro G).filtro z} > 1 := by

  -- Usamos el teorema card_congr_puntos_fijos usando la acción de conjugación (X = G)
  have h_card_ptfijos := card_congr_puntos_fijos (G := G) (X := G) p h_pgrupo

  -- Relacionamos los puntos fijos X0 con el Centro Z(G)
  have h_X0_centro : Fintype.card {x : G // PuntosFijos (G := G) (X := G) x} =
                     Fintype.card {z : G // (Centro G).filtro z} := by
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨x, hx⟩ => ⟨x, (fijos_conjugacion_eq_centro x).mp hx⟩,
      invFun := fun ⟨z, hz⟩ => ⟨z, (fijos_conjugacion_eq_centro z).mpr hz⟩,
      left_inv := fun _ => Subtype.ext rfl,
      right_inv := fun _ => Subtype.ext rfl
    }

  -- Sustituimos X0 por Z(G) en |G| ≡ |Z(G)| (mod p)
  rw [h_X0_centro] at h_card_ptfijos

  -- Como G es un p-grupo, |G| = p^m
  -- Como m ≥ 1, |G| es un múltiplo de p, por tanto |G| ≡ 0 (mod p)
  rcases h_pgrupo with ⟨hp_prime, m, hm_pos, hG_card⟩
  have h_G_mod_p : Fintype.card G ≡ 0 [MOD p] := by
    rw [orden_grupo] at hG_card
    rw [hG_card]
    -- Demostramos que p^m ≡ 0 [MOD p] viendo que p divide a p^m
    apply Nat.modEq_zero_iff_dvd.mpr
    -- Sabiendo que m > 0, lo dividimos en casos
    cases m with
    | zero =>
      -- Caso imposible porque m > 0
      omega
    | succ k =>
      -- Sabiendo que a | b significa ∃ c, b = a * c. Etonces  c = p^k
      exists (p ^ k)
      -- Ahora tenemos que demostrar p^(k+1) = p * p^k
      -- pow_succ lo convierte a p^k * p, y mul_comm le da la vuelta
      rw [Nat.pow_succ, mul_comm]

  -- Si 0 ≡ |G| y |G| ≡ |Z(G)|, entonces 0 ≡ |Z(G)| (mod p)
  have h_Z_mod_p : Fintype.card {z : G // (Centro G).filtro z} ≡ 0 [MOD p] := by
    -- h_card_ptfijos : |G| ≡ |Z(G)|, por tanto h_card_ptfijos.symm : |Z(G)| ≡ |G|
    -- h_G_mod_p : |G| ≡ 0
    exact Nat.ModEq.trans h_card_ptfijos.symm h_G_mod_p

  -- El centro siempre contiene al elemento neutro '1', luego su tamaño es al menos 1
  have h_Z_pos : Fintype.card {z : G // (Centro G).filtro z} ≥ 1 := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨1, (Centro G).neutro_sub⟩⟩

  -- Como p ∣ |Z(G)| y |Z(G)| ≥ 1, entonces |Z(G)| debe ser al menos p.
  have hp_ge_2 : p ≥ 2 := hp_prime.two_le
  have h_p_dvd_Z : p ∣ Fintype.card {z : G // (Centro G).filtro z} := Nat.modEq_zero_iff_dvd.mp h_Z_mod_p
  have h_Z_ge_p : Fintype.card {z : G // (Centro G).filtro z} ≥ p := Nat.le_of_dvd h_Z_pos h_p_dvd_Z

  exact Nat.lt_of_lt_of_le (by omega) h_Z_ge_p
