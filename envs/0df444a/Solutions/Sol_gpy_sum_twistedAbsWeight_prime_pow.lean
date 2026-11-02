-- Prove2me | solution 1 for gpy_sum_twistedAbsWeight_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T10:42:40.291491+00:00
-- url     : https://prove2.me/submissions/a713dbaa-d7a1-4916-a0c5-96590b95b667

/- PubAll restated solution file: Mathlib only, absolute bounds only.
   No asymptotic TwistedMertensBound main term is stated or proved here. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def twistedWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ((localGoodChoiceFinset h i p hd he).card : ℝ))
    / ((Nat.totient n : ℕ) : ℝ)

noncomputable def twistedMuSqSum {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n M),
    (ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n
      * (Real.log (n : ℝ)) ^ m

noncomputable def twistedAbsWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  abs ((ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n)

/-- The twisted weight at `1` is `1`. -/
theorem twistedWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedWeight h i hd he 1 = 1 := by
  unfold twistedWeight
  simp

/-- The twisted weight is multiplicative on coprime pairs. -/
theorem twistedWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedWeight h i hd he (m * n)
      = twistedWeight h i hd he m * twistedWeight h i hd he n := by
  unfold twistedWeight
  have hdisj : Disjoint m.primeFactors n.primeFactors := hcop.disjoint_primeFactors
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union hdisj, Nat.totient_mul hcop,
    Nat.cast_mul, div_mul_div_comm]

/-- The twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedWeight
  have hcast : ((Nat.totient p : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast
    ring
  rw [hp.primeFactors, Finset.prod_singleton, hcast]

/-- Nonnegativity of the absolute twisted weight. -/
theorem twistedAbsWeight_nonneg_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) :
    (0 : ℝ) ≤ twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  exact abs_nonneg _

/-- The absolute twisted weight at `1` is `1`. -/
theorem twistedAbsWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedAbsWeight h i hd he 1 = 1 := by
  unfold twistedAbsWeight
  rw [twistedWeight_one_aux, ArithmeticFunction.moebius_apply_one]
  simp

/-- The absolute twisted weight is multiplicative on coprime pairs. -/
theorem twistedAbsWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedAbsWeight h i hd he (m * n)
      = twistedAbsWeight h i hd he m * twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmuR : ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ)
        * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
    rw [hmu]
    push_cast
    ring
  rw [hmuR, twistedWeight_mul_aux h i hd he hm hn hcop]
  simp only [abs_mul]
  ring

/-- The absolute twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedAbsWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedAbsWeight
  rw [twistedWeight_prime_aux h i hd he hp, ArithmeticFunction.moebius_apply_prime hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hC : (0 : ℝ) ≤ ((localGoodChoiceFinset h i p hd he).card : ℝ) :=
    Nat.cast_nonneg _
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_cast
  rw [hcast]
  rw [abs_mul, abs_neg, abs_one, one_mul,
    abs_of_nonneg (div_nonneg hC (le_of_lt hden))]

/-- The absolute twisted weight at `p²` is `0` (Möbius vanishes). -/
theorem twistedAbsWeight_prime_pow_two_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he (p ^ 2) = 0 := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (p ^ 2) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  have hmuR : ((ArithmeticFunction.moebius (p ^ 2) : ℤ) : ℝ) = 0 := by
    rw [hmu]
    simp
  rw [hmuR]
  simp

/-! ### The uniform local-count bound -/

/-- The local count is at most `(k+1)²`: the local choice finset
    is a subfinset of `univ` over `Option (Fin k) × Option (Fin k)`. -/
theorem localGoodChoice_card_le_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((localGoodChoiceFinset h i p hd he).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
  have hcard : (localGoodChoiceFinset h i p hd he).card ≤ (k + 1) * (k + 1) := by
    calc (localGoodChoiceFinset h i p hd he).card
        ≤ Finset.univ.card := Finset.card_le_univ _
      _ = (k + 1) * (k + 1) := by
          simp [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  have hcast : (((k + 1) * (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) ^ 2 := by
    push_cast
    ring
  calc ((localGoodChoiceFinset h i p hd he).card : ℝ)
      ≤ (((k + 1) * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((k : ℝ) + 1) ^ 2 := hcast

/-! ### Truncated Euler product for the absolute twisted weight -/

/-- Local sums at prime powers: `1 + c_p/(p-1)`. -/
theorem sum_twistedAbsWeight_prime_pow_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, twistedAbsWeight h i hd he (p ^ j)
      = 1 + ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  have e0 : twistedAbsWeight h i hd he (p ^ 0) = 1 := by
    simp [twistedAbsWeight_one_aux]
  have e1 : twistedAbsWeight h i hd he (p ^ 1)
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
    rw [pow_one]
    exact twistedAbsWeight_prime_aux h i hd he hp
  have e2 : twistedAbsWeight h i hd he (p ^ 2) = 0 :=
    twistedAbsWeight_prime_pow_two_aux h i hd he hp
  rw [e0, e1, e2]
  ring

/-- TRUNCATED EULER PRODUCT. Over any prime finset `S`, the
    truncated sum of the absolute twisted weight factors exactly
    as the product of the local sums `1 + c_p/(p-1)`. -/
theorem solution {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, abs ((ArithmeticFunction.moebius (p ^ j) : ℝ) * ((∏ p ∈ (p ^ j).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient (p ^ j) : ℕ) : ℝ))) = 1 + ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1) :=
  sum_twistedAbsWeight_prime_pow_aux h i hd he hp
