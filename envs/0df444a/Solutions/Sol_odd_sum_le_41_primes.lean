-- Prove2me | solution 1 for odd_sum_le_41_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T03:35:42.293993+00:00
-- url     : https://prove2.me/submissions/623f7295-edc8-4175-89a4-0d9e25ca55a7

import Mathlib
import Definitions.Def_Schnir_defs
import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_PrimePairSieve_divisor_kernel_comparison
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold
import Theorems.Thm_PrimePairSieve_reciprocal_weighted_sifted_bound
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Theorems.Thm_Schnir_basis_of_density
import Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound

/-!
Every odd `n > 1` is a sum of at most `41` primes.

`A = B + B` with `B = {(p - 3)/2 : p odd prime}`; we show `σ(A) ≥ 1/20` and apply Mann's theorem
(platform `Schnir.basis_of_density`), giving `40` odd primes plus one `3`.
* `n ≤ 200`: `A ⊇ [1, 10]`;
* `log(2N+3) < 30`: Chebyshev's `ψ(x) ≥ a x - 5 log x + 5` (`a ≈ 0.9212`) via `ψ(x) ≤ π(x) log x`;
* `30 ≤ log n ≤ 2000`: Riesel–Vaughan small shifts with the first `150` odd primes; prime pairs
  bounded by the platform's `TaoFivePrimes.siebert_prime_pair_bound`, with
  `∑_{b<a} K(a-b) ≤ 19496` (`K(d) = ∏_{p ∣ d, p > 2} (p-1)/(p-2)`) checked by the kernel;
* `log n ≥ 2000`: Goldbach analogue of Siebert's bound `r(s) ≤ 8 C K(s) s/log² s + O(√s)` from the
  platform's `PrimePairSieve` nodes (shift `d = 2sP - s`), the weighted first moment, and Hölder
  with `∑ K(s)^12 ≤ 19500 x`.
-/

-- ===== Cheb =====
/-! Chebyshev's lower bound `ψ(x) ≥ a x - 5 log x + 5` for `x ≥ 30`, `a ≈ 0.92129`
(ported from PrimeNumberTheoremAnd, `IEANTN/Chebyshev.lean`, with explicit `log 3`, `log 5` bounds). -/

namespace Chebyshev
open Real

theorem Ioc_eq_Icc {n : ℕ} : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

theorem log3_bounds : 1.0986 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0987 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 - 1/4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

theorem log5_bounds : 1.60943 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.60944 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/5 : ℝ) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 - 1/5 : ℝ) = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]


open Real Finsupp Finset
open ArithmeticFunction hiding log

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop ( disch := positivity )
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.9212 0.9214 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log3_bounds.1, log3_bounds.2, log5_bounds.1, log5_bounds.2]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, log3_bounds.1, log5_bounds.1]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

end Chebyshev

-- ===== LargeBase =====
/-! Unchanged helper lemmas from the proved `241` entry (Schnirelmann large range). -/

open Finset Real

namespace P41
open Schnir

def s6P (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

lemma s6_card_P (M : ℕ) (hM : 2 ≤ M) : (s6P M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : s6P M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [s6P, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- `∑_{s ≤ n} r s ≥ ∑_{p ∈ P(K)} Q(n - p)` for `K ≤ n`. -/
lemma s6_pairs (n K : ℕ) (hK : K ≤ n) :
    ∑ p ∈ s6P K, (s6P (n - p)).card ≤ ∑ s ∈ range (n + 1), r s := by
  unfold r
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun pq => (⟨pq.1 + pq.2, pq.1⟩ : Σ _ : ℕ, ℕ))
  · intro pq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, s6P, Finset.mem_filter, Finset.mem_range] at hpq ⊢
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hpq
    refine ⟨by omega, by omega, h2, h3, ?_, ?_⟩
    · rw [Nat.add_sub_cancel_left]; exact h5
    · rw [Nat.add_sub_cancel_left]; exact h6
  · intro a _ b _ hab
    simp only [Sigma.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have h2' : a.1 = b.1 := eq_of_heq h2
    exact Sigma.ext h2' (heq_of_eq (by omega))

lemma s6_Ico_card (p K : ℕ) : ((range K).filter (fun t => p ≤ t)).card = K - p := by
  have : (range K).filter (fun t => p ≤ t) = Ico p K := by
    ext t; simp [Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- `∑_{p ∈ P(K)} (K - p) = ∑_{t < K} Q(t)`. -/
lemma s6_swap (K : ℕ) : ∑ p ∈ s6P K, (K - p) = ∑ t ∈ range K, (s6P t).card := by
  have h1 : ∀ p ∈ s6P K, K - p = ∑ t ∈ range K, if p ≤ t then 1 else 0 := by
    intro p _
    rw [Finset.sum_boole, ← s6_Ico_card p K]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  congr 1
  ext p
  simp only [s6P, Finset.mem_filter, Finset.mem_range] at ht ⊢
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩

/-- Summation by parts, as an inequality. -/
lemma s6_abel (a w L : ℕ → ℝ) (n0 : ℕ)
    (hw : ∀ k, n0 < k → w (k + 1) ≤ w k)
    (hML : ∀ k, n0 < k → L k ≤ ∑ s ∈ range (k + 1), a s) :
    ∀ n, n0 ≤ n →
      ∑ s ∈ Ioc n0 n, (L s - L (s - 1)) * w s
        + (∑ s ∈ range (n + 1), a s - L n) * w (n + 1)
        - (∑ s ∈ range (n0 + 1), a s - L n0) * w (n0 + 1)
      ≤ ∑ s ∈ Ioc n0 n, a s * w s := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ioc_succ_top hk, Finset.sum_Ioc_succ_top hk, Finset.sum_range_succ _ (k + 1)]
    have h1 := hML (k + 1) (by omega)
    have h2 := hw (k + 1) (by omega)
    rw [Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel] at ih ⊢
    have h3 : 0 ≤ (∑ s ∈ range (k + 1), a s + a (k + 1) - L (k + 1)) * (w (k + 1) - w (k + 1 + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem s6_r_le (s : ℕ) : r s ≤ s := by
  unfold r
  calc _ ≤ (Finset.Icc 1 s).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        have := hp.2.1.one_lt
        simp only [Finset.mem_Icc]; omega
    _ = s := by simp

theorem s6_r_odd (s : ℕ) (hs : ¬ Even s) : r s = 0 := by
  unfold r
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ⟨hpp, hp2, hqp, hq2⟩
  simp only [Finset.mem_range] at hp
  have h1 := hpp.odd_of_ne_two hp2
  have h2 := hqp.odd_of_ne_two hq2
  have : Even (p + (s - p)) := Odd.add_odd h1 h2
  rw [Nat.add_sub_cancel' (by omega)] at this
  exact hs this

theorem s6_mono (a b : ℝ) (ha : 130 ≤ a) (hab : a ≤ b) :
    Real.exp a / a ^ 2 ≤ Real.exp b / b ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : b ≤ a * (1 + (b - a) / 2) := by nlinarith
  have h2 : 1 + (b - a) / 2 ≤ Real.exp ((b - a) / 2) := by
    have := Real.add_one_le_exp ((b - a) / 2); linarith
  have h3 : b ≤ a * Real.exp ((b - a) / 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 ha0.le)
  have h4 : b ^ 2 ≤ a ^ 2 * Real.exp (b - a) := by
    have : Real.exp (b - a) = Real.exp ((b - a) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ hb0.le h3 2
  have h5 : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h5]
  have := Real.exp_pos a
  nlinarith

/-- The weight `(log t)^2 / t` decreases past `e^130`. -/
theorem s6_w_anti (k : ℝ) (hk : Real.exp 130 ≤ k) :
    Real.log (k + 1) ^ 2 / (k + 1) ≤ Real.log k ^ 2 / k := by
  have hk0 : 0 < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hu : 130 ≤ Real.log k := by
    have := Real.log_le_log (Real.exp_pos 130) hk
    rwa [Real.log_exp] at this
  have huv : Real.log k ≤ Real.log (k + 1) := Real.log_le_log hk0 (by linarith)
  have h := s6_mono _ _ hu huv
  rw [Real.exp_log hk0, Real.exp_log (by linarith)] at h
  have hv : 0 < Real.log (k + 1) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h ⊢
  linarith

end P41

-- ===== GS =====
/-! Goldbach analogue of Siebert's bound: `r(s) ≤ 8 C K(s) (s+1)/log²(s+1) + √(s+1)/2 + 2`,
from the platform's proved weighted large-sieve bound for sifted sets, the divisor-kernel
comparison and the base-denominator threshold. The Goldbach set `{p : s - p prime}` is sifted
by `n (n + d)` with `d = 2 s P - s`, `P` the primorial of the sieve level, so that `p ∣ d ↔ p ∣ s`
for every sieving prime `p`. -/

open Finset Real

namespace P41
open Schnir

/-- singular-series weight `K(s) = ∏_{p ∣ s, p > 2} (p-1)/(p-2)`. -/
noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

noncomputable def bfun (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)

noncomputable def gfun (d n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, if p ∣ d then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)

theorem Kf_factor_ge_one (p : ℕ) : (1 : ℝ) ≤ if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  split_ifs with h
  · have : (2 : ℝ) < p := by exact_mod_cast h
    rw [le_div_iff₀ (by linarith)]; linarith
  · exact le_rfl

theorem one_le_Kf (s : ℕ) : 1 ≤ Kf s := by
  unfold Kf
  calc (1 : ℝ) = ∏ p ∈ s.primeFactors, (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => by norm_num) (fun p _ => Kf_factor_ge_one p)

theorem bfun_nonneg (n : ℕ) : 0 ≤ bfun n := by
  unfold bfun
  apply prod_nonneg
  intro p hp
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs with h
  · norm_num
  · have : (3 : ℝ) ≤ p := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    apply div_nonneg (by norm_num); linarith

/-- squarefree numbers `≤ Z` are exactly the divisors of `Z#` that are `≤ Z`. -/
theorem divisors_primorial_filter (Z : ℕ) :
    (primorial Z).divisors.filter (fun n => n ≤ Z) = (Icc 1 Z).filter Squarefree := by
  ext n
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hle⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos hdvd (primorial_pos Z), hle⟩, ?_⟩
    exact (squarefree_primorial Z).squarefree_of_dvd hdvd
  · rintro ⟨⟨h1, hle⟩, hsq⟩
    exact ⟨⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hle), primorial_ne_zero Z⟩, hle⟩

/-- a sum over divisors of `Z#` of a function vanishing above `Z`. -/
theorem sum_divisors_primorial (Z : ℕ) (f : ℕ → ℝ) (hf : ∀ n, Z < n → f n = 0) :
    ∑ n ∈ (primorial Z).divisors, f n = ∑ n ∈ (Icc 1 Z).filter Squarefree, f n := by
  rw [← divisors_primorial_filter, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rfl
  · exact hf n (by omega)

theorem threshold_ge (z : ℝ) (hz : 40 ≤ z) :
    (log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by
  have hT := PrimePairSieve.reciprocal_base_denominator_dominates_threshold z hz
  obtain ⟨hC1, -, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  set C := TaoFivePrimes.twinPrimeConstant
  set T := (log (4 * z)) ^ 2 / (2 * C) with hTdef
  have hT0 : 0 ≤ T := by positivity
  -- `log (4z) ≤ 2 √(4z)`, so `T ≤ 16 z / 2.5`
  have hy : 0 < 4 * z := by linarith
  have hl0 : 0 ≤ log (4 * z) := log_nonneg (by linarith)
  have hl : log (4 * z) ≤ 2 * √(4 * z) := by
    have h := log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
    rw [Real.log_sqrt hy.le] at h
    linarith
  have hl2 : (log (4 * z)) ^ 2 ≤ 16 * z := by
    have := pow_le_pow_left₀ hl0 hl 2
    rw [mul_pow, Real.sq_sqrt hy.le] at this
    linarith
  have hTle : T ≤ 32 / 5 * z := by
    rw [hTdef, div_le_iff₀ (by positivity)]
    nlinarith
  set x := (z + 1) * T / (16 * z ^ 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [hx, div_lt_one (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hTle (by linarith : (0 : ℝ) ≤ z + 1)
    have h2 : (z + 1) * (32 / 5 * z) < 16 * z ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hz (by linarith : (0 : ℝ) ≤ z)]
    linarith
  have : T ≤ T / (1 - x) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact this.trans hT

set_option maxHeartbeats 1000000 in
/-- Goldbach analogue of Siebert's bound, uniform in even `s ≥ 25599`. -/
theorem gs_main (s : ℕ) (hs : Even s) (hs1 : 25599 ≤ s) :
    (r s : ℝ) ≤ 8 * TaoFivePrimes.twinPrimeConstant * Kf s * ((s : ℝ) + 1) /
      (log ((s : ℝ) + 1)) ^ 2 + √((s : ℝ) + 1) / 2 + 2 := by
  set N := s + 1 with hNdef
  have hNR : (N : ℝ) = (s : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  have hs1R : (25599 : ℝ) ≤ s := by exact_mod_cast hs1
  have hNpos : (0 : ℝ) < N := by rw [hNR]; linarith
  set z : ℝ := √(N : ℝ) / 4 with hz
  have hsq : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hNpos.le
  have hz40 : 40 ≤ z := by
    have : (160 : ℝ) ≤ √(N : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hNpos.le]; rw [hNR]; linarith
    rw [hz]; linarith
  have hzpos : 0 < z := by linarith
  have hzN : 16 * z ^ 2 = N := by rw [hz, div_pow, hsq]; ring
  set Z := ⌊z⌋₊ with hZ
  have hZz : (Z : ℝ) ≤ z := Nat.floor_le hzpos.le
  have hZ1 : 1 ≤ Z := Nat.le_floor (by norm_num; linarith)
  have hzZ : ∀ n : ℕ, Z < n → z < n := by
    intro n hn
    have h1 : z < (Z : ℝ) + 1 := Nat.lt_floor_add_one z
    have h2 : (Z : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  set P := primorial Z with hP
  have hP1 : 1 ≤ P := primorial_pos Z
  set M := 2 * s * P with hM
  have hsM : s ≤ M := by
    rw [hM]; nlinarith
  set d := M - s with hd
  have hd2 : 2 ∣ d := by
    obtain ⟨k, hk⟩ := hs
    have hM2 : 2 ∣ M := ⟨s * P, by rw [hM]; ring⟩
    exact Nat.dvd_sub hM2 ⟨k, by omega⟩
  have hpM : ∀ p, p.Prime → p ≤ Z → p ∣ M := fun p hp hpZ =>
    Dvd.dvd.mul_left ((hp.dvd_primorial_iff).2 hpZ) _
  have hpd : ∀ p, p.Prime → p ≤ Z → p ∣ d → p ∣ s := by
    intro p hp hpZ h
    have h1 := hpM p hp hpZ
    have hdM : d + s = M := by omega
    rw [← hdM] at h1
    exact (Nat.dvd_add_right h).1 h1
  -- the sifted set
  set A := (range N).filter (fun n : ℕ => n.Prime ∧ z < n ∧ n ≤ s ∧ (s - n).Prime ∧
    z < ((s - n : ℕ) : ℝ)) with hA
  set Q : Finset ℕ+ := (Finset.Icc (1 : ℕ+) (Nat.toPNat' Z)).filter (fun q => Squarefree (q : ℕ))
    with hQ
  have hmemQ : ∀ q : ℕ+, q ∈ Q ↔ (1 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Z) ∧ Squarefree (q : ℕ) := by
    intro q
    rw [hQ, mem_filter, mem_Icc, ← PNat.coe_le_coe, ← PNat.coe_le_coe, Nat.toPNat'_coe,
      if_pos (by omega)]
    simp
  have hQ1 : (1 : ℕ+) ∈ Q := by
    rw [hmemQ]; simp [hZ1]
  have hQz : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z := by
    intro q hq
    rw [hmemQ] at hq
    refine ⟨hq.2, ?_⟩
    have : ((q : ℕ) : ℝ) ≤ Z := by exact_mod_cast hq.1.2
    linarith
  have hAN : A ⊆ range N := filter_subset _ _
  have hAs : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n * (n + d) := by
    intro q hq n hn p hp hdvd
    rw [hmemQ] at hq
    rw [hA, mem_filter] at hn
    obtain ⟨-, hnp, hzn, hns, hsnp, hzsn⟩ := hn
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpq : p ≤ (q : ℕ) := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    have hpZ : p ≤ Z := hpq.trans hq.1.2
    have hpz : (p : ℝ) ≤ z := by
      have : (p : ℝ) ≤ Z := by exact_mod_cast hpZ
      linarith
    rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpp hnp).1 h
      subst this; linarith
    · have e : n + d = M - (s - n) := by omega
      rw [e] at h
      have h2 : p ∣ s - n := by
        have h1 := hpM p hpp hpZ
        have hsum : M - (s - n) + (s - n) = M := by omega
        rw [← hsum] at h1
        exact (Nat.dvd_add_right h).1 h1
      have := (Nat.prime_dvd_prime_iff_eq hpp hsnp).1 h2
      rw [← this] at hzsn; linarith
  have hsieve := PrimePairSieve_reciprocal_weighted_sifted_bound Q hQ1 N d z (by linarith)
    hQz hd2 A hAN hAs
  -- the kernel `F`
  set F : ℕ → ℝ := fun n => if (n : ℝ) ≤ z then 1 / ((N : ℝ) + 16 * n * z) else 0 with hF
  have hFanti : Antitone F := by
    intro a b hab
    simp only [hF]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    split_ifs with h1 h2 h2
    · apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    · linarith
    · positivity
    · exact le_rfl
  have hFvan : ∀ (f : ℕ → ℝ) (n : ℕ), Z < n → f n * F n = 0 := by
    intro f n hn
    have := hzZ n hn
    simp only [hF, if_neg (not_le.2 this), mul_zero]
  set Sq := (Icc 1 Z).filter Squarefree with hSq
  have hQmap : Q.map ⟨PNat.val, PNat.coe_injective⟩ = Sq := by
    ext n
    simp only [mem_map, Function.Embedding.coeFn_mk, hSq, mem_filter, mem_Icc]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (hmemQ q).1 hq
    · rintro h
      refine ⟨⟨n, by omega⟩, (hmemQ _).2 h, rfl⟩
  have hFon : ∀ n ∈ Sq, F n = 1 / ((N : ℝ) + 16 * n * z) := by
    intro n hn
    rw [hSq, mem_filter, mem_Icc] at hn
    have : (n : ℝ) ≤ Z := by exact_mod_cast hn.1.2
    simp only [hF, if_pos (this.trans hZz)]
  -- the sieve sum
  set X := ∑ q ∈ Q, (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) /
      ((N : ℝ) + 16 * ((q : ℕ) : ℝ) * z) with hXdef
  have hX : X = ∑ n ∈ P.divisors, gfun d n * F n := by
    rw [sum_divisors_primorial Z _ (hFvan _), hXdef, ← hSq, ← hQmap, sum_map]
    refine sum_congr rfl fun q hq => ?_
    have hn : (q : ℕ) ∈ Sq := by rw [← hQmap]; exact mem_map_of_mem _ hq
    have e : (⟨PNat.val, PNat.coe_injective⟩ : ℕ+ ↪ ℕ) q = (q : ℕ) := rfl
    rw [e, hFon _ hn, gfun]; ring
  set Bt := ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) with hBt
  have hBt' : Bt = ∑ n ∈ Sq, bfun n / (1 + n / z) := by
    rw [hBt, ← hZ, hSq, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [bfun]
  have hY : ∑ n ∈ P.divisors, bfun n * F n = Bt / N := by
    rw [sum_divisors_primorial Z _ (hFvan _), hBt', sum_div]
    refine sum_congr rfl fun n hn => ?_
    rw [hFon n hn]
    have h1 : (N : ℝ) + 16 * n * z = N * (1 + n / z) := by
      rw [← hzN]; field_simp
    rw [h1]; field_simp
  have hK := PrimePairSieve.divisor_kernel_comparison P d (squarefree_primorial Z) hd2 F hFanti
  have hKp : (∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) ≤ Kf s := by
    rw [← prod_filter, Kf, ← prod_filter]
    apply prod_le_prod_of_subset_of_one_le
    · intro p hp
      rw [mem_filter, Nat.mem_primeFactors] at hp ⊢
      obtain ⟨⟨hpp, hpP, -⟩, h2, hpdv⟩ := hp
      have hpZ := (hpp.dvd_primorial_iff).1 hpP
      exact ⟨⟨hpp, hpd p hpp hpZ hpdv, by omega⟩, h2⟩
    · intro p hp
      have h2 := (mem_filter.1 hp).2.1
      have : (2 : ℝ) < p := by exact_mod_cast h2
      apply div_nonneg (by linarith) (by linarith)
    · intro p hp _
      have h2 := (mem_filter.1 hp).2
      have := Kf_factor_ge_one p
      rwa [if_pos h2] at this
  -- assemble
  have hBT := threshold_ge z hz40
  obtain ⟨hC1, -, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  set C := TaoFivePrimes.twinPrimeConstant with hCdef
  have h4z : 4 * z = √(N : ℝ) := by rw [hz]; ring
  have hlog : log (4 * z) = log N / 2 := by rw [h4z, Real.log_sqrt hNpos.le]
  have hlogN : 0 < log (N : ℝ) := log_pos (by rw [hNR]; linarith)
  set T := (log (4 * z)) ^ 2 / (2 * C) with hTdef
  have hTpos : 0 < T := by rw [hTdef, hlog]; positivity
  have hBpos : 0 < Bt := lt_of_lt_of_le hTpos hBT
  have hKs := one_le_Kf s
  have hYX : Bt / N ≤ X * Kf s := by
    rw [← hY, hX]
    have hX0 : 0 ≤ ∑ n ∈ P.divisors, gfun d n * F n := by
      rw [← hX, hXdef]
      apply sum_nonneg; intro q hq
      apply div_nonneg _ (by positivity)
      apply prod_nonneg; intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      split_ifs with h
      · apply div_nonneg (by norm_num); linarith
      · have hp2' : p ≠ 2 := fun h2 => h (h2 ▸ hd2)
        have : (3 : ℝ) ≤ p := by
          have : 3 ≤ p := by omega
          exact_mod_cast this
        apply div_nonneg (by norm_num); linarith
    exact hK.trans (mul_le_mul_of_nonneg_left hKp hX0)
  have hXpos : 0 < X := by
    have : 0 < X * Kf s := lt_of_lt_of_le (by positivity) hYX
    exact pos_of_mul_pos_left this (by linarith)
  have hAcard : (A.card : ℝ) ≤ 8 * C * Kf s * N / (log N) ^ 2 := by
    refine hsieve.trans ?_
    rw [inv_le_iff_one_le_mul₀' hXpos]
    have h1 : T / N ≤ X * Kf s := (div_le_div_of_nonneg_right hBT hNpos.le).trans hYX
    have e : 8 * C * Kf s * N / (log N) ^ 2 = Kf s * N / T := by
      rw [hTdef, hlog]; field_simp; ring
    rw [e]
    rw [div_le_iff₀ hNpos] at h1
    rw [← mul_div_assoc, le_div_iff₀ hTpos]
    nlinarith
  -- `r s ≤ |A| + 2 (Z + 1)`
  have hr : r s ≤ A.card + (Z + 1) + (Z + 1) := by
    unfold r
    have hsub : (range (s + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (s - p).Prime ∧ s - p ≠ 2) ⊆
        A ∪ range (Z + 1) ∪ (range (Z + 1)).image (fun q => s - q) := by
      intro p hp
      rw [mem_filter, mem_range] at hp
      obtain ⟨hps, hpp, -, hsp, -⟩ := hp
      by_cases h1 : (p : ℝ) ≤ z
      · apply mem_union_left; apply mem_union_right
        exact mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h1))
      by_cases h2 : ((s - p : ℕ) : ℝ) ≤ z
      · apply mem_union_right
        exact mem_image.2 ⟨s - p, mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h2)), by omega⟩
      · apply mem_union_left; apply mem_union_left
        rw [hA, mem_filter, mem_range]
        exact ⟨by omega, hpp, not_le.1 h1, by omega, hsp, not_le.1 h2⟩
    calc _ ≤ (A ∪ range (Z + 1) ∪ (range (Z + 1)).image (fun q => s - q)).card := card_le_card hsub
      _ ≤ (A ∪ range (Z + 1)).card + ((range (Z + 1)).image (fun q => s - q)).card := card_union_le _ _
      _ ≤ A.card + (range (Z + 1)).card + (range (Z + 1)).card :=
          add_le_add (card_union_le _ _) card_image_le
      _ = _ := by rw [card_range]
  have hr' : (r s : ℝ) ≤ A.card + 2 * z + 2 := by
    have : (r s : ℝ) ≤ A.card + (Z + 1) + (Z + 1) := by exact_mod_cast hr
    linarith
  rw [hNR] at hAcard
  have : 2 * z = √((s : ℝ) + 1) / 2 := by rw [hz, hNR]; ring
  linarith

end P41

-- ===== KMom =====
/-! Twelfth moment of the singular-series weight: `∑_{s ≤ x, s even} K(s)^12 ≤ 19500 x`. -/

open Finset Real

namespace P41

noncomputable def kb (p : ℕ) : ℝ := ((((p : ℝ) - 1) / ((p : ℝ) - 2)) ^ 12 - 1) / p

lemma kb_nonneg (p : ℕ) (hp : 3 ≤ p) : 0 ≤ kb p := by
  unfold kb
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  apply div_nonneg _ (by linarith)
  have : 1 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  have := one_le_pow₀ (n := 12) this
  linarith

lemma kb_exp_le (t : ℝ) (ht : t < 1) : exp t ≤ 1 / (1 - t) := by
  have h := Real.add_one_le_exp (-t)
  rw [le_div_iff₀ (by linarith)]
  have : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

lemma kb_le (p : ℕ) (hp : 211 ≤ p) : kb p ≤ 13 * (1 / ((p : ℝ) - 1) ^ 2) := by
  have h : (211 : ℝ) ≤ p := by exact_mod_cast hp
  set t : ℝ := 1 / ((p : ℝ) - 2) with ht
  have ht0 : 0 < t := by rw [ht]; apply div_pos one_pos; linarith
  have h12t : 12 * t ≤ 12 / 209 := by
    rw [ht]; rw [mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have e1 : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + t := by
    rw [ht, one_add_div hp2]; congr 1; ring
  have hpow : (1 + t) ^ 12 ≤ 1 / (1 - 12 * t) := by
    calc (1 + t) ^ 12 ≤ exp t ^ 12 := by
          apply pow_le_pow_left₀ (by linarith); linarith [Real.add_one_le_exp t]
      _ = exp (12 * t) := by rw [← exp_nat_mul]; norm_num
      _ ≤ 1 / (1 - 12 * t) := kb_exp_le _ (by linarith)
  have hq : (1 + t) ^ 12 - 1 ≤ 12 * t / (1 - 12 * t) := by
    have hne : 1 - 12 * t ≠ 0 := by linarith
    have : 1 / (1 - 12 * t) - 1 = 12 * t / (1 - 12 * t) := by
      rw [div_sub_one hne]; congr 1; ring
    linarith
  -- `12 t / (1 - 12 t) = 12 / (p - 14)`
  have e3 : 1 - 12 * t = ((p : ℝ) - 14) / ((p : ℝ) - 2) := by
    rw [ht, mul_one_div, eq_div_iff hp2, sub_mul, div_mul_cancel₀ _ hp2]; ring
  have e2 : 12 * t / (1 - 12 * t) = 12 / ((p : ℝ) - 14) := by
    rw [e3, ht, mul_one_div, div_div_div_cancel_right₀ hp2]
  unfold kb
  rw [e1]
  have hp0 : (0 : ℝ) < p := by linarith
  calc ((1 + t) ^ 12 - 1) / p ≤ 12 / ((p : ℝ) - 14) / p := by
        rw [← e2]; exact div_le_div_of_nonneg_right hq hp0.le
    _ ≤ 13 * (1 / ((p : ℝ) - 1) ^ 2) := by
        rw [div_div, mul_one_div, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith

lemma kb_tail (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p ∧ 211 ≤ p) :
    ∀ m : ℕ, 209 ≤ m → (∀ p ∈ Q, p ≤ m) →
      ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 418 - 1 / (2 * (m : ℝ)) := by
  induction Q using Finset.induction_on_max with
  | empty =>
    intro m hm _
    have : (209 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < m := by linarith
    simp only [sum_empty]
    rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  | insert a s hlt ih =>
    intro m hm hle
    have ha := hQ a (mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert has]
    have ih' := ih (fun p hp => hQ p (mem_insert_of_mem hp)) (a - 2) (by omega) (by
      intro p hp
      have h1 := hlt p hp
      have h2 := (hQ p (mem_insert_of_mem hp)).1
      obtain ⟨k, hk⟩ := h2
      obtain ⟨j, hj⟩ := ha.1
      omega)
    have hcast : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at ih'
    have haR : (211 : ℝ) ≤ a := by exact_mod_cast ha.2
    have hma : (a : ℝ) ≤ m := by exact_mod_cast hle a (mem_insert_self a s)
    have key : 1 / ((a : ℝ) - 1) ^ 2 ≤ 1 / (2 * ((a : ℝ) - 2)) - 1 / (2 * (a : ℝ)) := by
      rw [div_sub_div _ _ (by nlinarith) (by nlinarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    have hm2 : 1 / (2 * (m : ℝ)) ≤ 1 / (2 * (a : ℝ)) := by
      apply one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

def Smallp : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199}

set_option maxHeartbeats 4000000 in
lemma small_prod : ∏ p ∈ Smallp, (1 + kb p) ≤ 37695 := by
  simp only [Smallp, kb]
  norm_num

set_option maxHeartbeats 4000000 in
lemma kb_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ P, (1 + kb p) ≤ 37695 * (1 / (1 - 13 / 418)) := by
  set Q := P.filter (fun p => 211 ≤ p) with hQdef
  have hsub : P ⊆ Smallp ∪ Q := by
    intro p hp
    obtain ⟨hpr, hp2⟩ := hP p hp
    by_cases h : 211 ≤ p
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
    · apply mem_union_left
      have hall : ∀ q ∈ range 211, Nat.Prime q → q ≠ 2 → q ∈ Smallp := by decide +kernel
      exact hall p (mem_range.2 (by omega)) hpr hp2
  have hdisj : Disjoint Smallp Q := by
    rw [Finset.disjoint_left]
    intro a ha haQ
    have := (mem_filter.1 haQ).2
    simp [Smallp] at ha; omega
  have hge : ∀ p ∈ Smallp ∪ Q, 3 ≤ p := by
    intro p hp
    rcases mem_union.1 hp with h | h
    · simp [Smallp] at h; omega
    · have := (mem_filter.1 h).2; omega
  have h1 : ∏ p ∈ P, (1 + kb p) ≤ ∏ p ∈ Smallp ∪ Q, (1 + kb p) :=
    prod_le_prod_of_subset_of_one_le hsub
      (fun i hi => by linarith [kb_nonneg i (hge i (hsub hi))])
      (fun i hi _ => by linarith [kb_nonneg i (hge i hi)])
  rw [prod_union hdisj] at h1
  have hQodd : ∀ p ∈ Q, Odd p ∧ 211 ≤ p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(hP p hp1).1.odd_of_ne_two (hP p hp1).2, hp2⟩
  have hsum : ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 418 := by
    have := kb_tail Q hQodd (max 209 (Q.sup id)) (le_max_left _ _)
      (fun p hp => le_max_of_le_right (le_sup (f := id) hp))
    have h9 : (0 : ℝ) ≤ 1 / (2 * ((max 209 (Q.sup id) : ℕ) : ℝ)) := by positivity
    linarith
  have hbsum : ∑ p ∈ Q, kb p ≤ 13 / 418 := by
    calc ∑ p ∈ Q, kb p ≤ ∑ p ∈ Q, 13 * (1 / ((p : ℝ) - 1) ^ 2) :=
          sum_le_sum (fun p hp => kb_le p (hQodd p hp).2)
      _ = 13 * ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
      _ ≤ 13 * (1 / 418) := by gcongr
      _ = 13 / 418 := by norm_num
  have hkb0 : ∀ p ∈ Q, 0 ≤ kb p := fun p hp => kb_nonneg p (by have := (hQodd p hp).2; omega)
  have hQprod : ∏ p ∈ Q, (1 + kb p) ≤ 1 / (1 - 13 / 418) := by
    calc ∏ p ∈ Q, (1 + kb p) ≤ ∏ p ∈ Q, exp (kb p) :=
          prod_le_prod (fun p hp => by linarith [hkb0 p hp]) (fun p _ => by linarith [Real.add_one_le_exp (kb p)])
      _ = exp (∑ p ∈ Q, kb p) := (Real.exp_sum _ _).symm
      _ ≤ exp (13 / 418) := exp_le_exp.2 hbsum
      _ ≤ 1 / (1 - 13 / 418) := kb_exp_le _ (by norm_num)
  have hQ1 : 0 ≤ ∏ p ∈ Q, (1 + kb p) := prod_nonneg (fun i hi => by linarith [hkb0 i hi])
  calc ∏ p ∈ P, (1 + kb p) ≤ (∏ p ∈ Smallp, (1 + kb p)) * ∏ p ∈ Q, (1 + kb p) := h1
    _ ≤ 37695 * (1 / (1 - 13 / 418)) := by
        apply mul_le_mul small_prod hQprod hQ1 (by norm_num)

lemma k_card (N : ℕ) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ p ≠ 2) :
    (((Icc 1 N).filter Even).filter (fun s => ∀ p ∈ U, p ∣ s)).card
      ≤ N / (2 * ∏ p ∈ U, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card
  intro s hs
  simp only [mem_filter, mem_Icc, mem_Ioc] at hs ⊢
  obtain ⟨⟨⟨h1, h2⟩, hev⟩, hdiv⟩ := hs
  refine ⟨⟨by omega, h2⟩, ?_⟩
  have h2U : (2 : ℕ) ∉ U := fun h => (hU 2 h).2 rfl
  have : 2 * ∏ p ∈ U, p = ∏ p ∈ insert 2 U, p := by rw [prod_insert h2U]
  rw [this]
  apply Finset.prod_primes_dvd
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Nat.prime_iff.1 (hU a ha).1
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact even_iff_two_dvd.1 hev
    · exact hdiv a ha

lemma k_mul_b (p : ℕ) (hp : p ≠ 0) :
    (p : ℝ) * kb p = (((p : ℝ) - 1) / ((p : ℝ) - 2)) ^ 12 - 1 := by
  unfold kb
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp

lemma k_pointwise (N s : ℕ) (hs : s ∈ (Icc 1 N).filter Even) :
    Kf s ^ 12 = ∑ U ∈ ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).powerset,
      if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * kb p) else 0 := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  simp only [mem_filter, mem_Icc] at hs
  obtain ⟨⟨h1, h2⟩, hev⟩ := hs
  have hs0 : s ≠ 0 := by omega
  have h2s : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hev, hs0⟩
  unfold Kf
  rw [← prod_pow, ← mul_prod_erase _ _ h2s]
  simp only [lt_irrefl, if_false, one_pow, one_mul]
  simp_rw [← prod_ite_zero]
  rw [← prod_one_add]
  have hset : s.primeFactors.erase 2 = P.filter (fun p => p ∣ s) := by
    ext p
    simp only [mem_erase, Nat.mem_primeFactors, mem_filter, P, mem_range]
    constructor
    · rintro ⟨hp2, hpr, hdvd, -⟩
      exact ⟨⟨by have := Nat.le_of_dvd (by omega) hdvd; omega, hpr, hp2⟩, hdvd⟩
    · rintro ⟨⟨-, hpr, hp2⟩, hdvd⟩
      exact ⟨hp2, hpr, hdvd, hs0⟩
  rw [hset, prod_filter]
  apply prod_congr rfl
  intro p hp
  have hpp := (mem_filter.1 hp).2
  have hp0 : p ≠ 0 := hpp.1.ne_zero
  have hp3 : 2 < p := by have := hpp.1.two_le; have := hpp.2; omega
  split_ifs
  · rw [k_mul_b p hp0]; ring
  · simp

/-- Twelfth moment: `∑_{s ≤ x, s even} K(s)^12 ≤ 19500 x`. -/
theorem k_mean (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (Kf s) ^ 12 ≤ 19500 * x := by
  set N := ⌊x⌋₊
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.1 hp).2
  set E := (Icc 1 N).filter Even
  rw [sum_congr rfl (fun s hs => k_pointwise N s hs), sum_comm]
  have hterm : ∀ U ∈ P.powerset,
      ∑ s ∈ E, (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * kb p) else 0)
        ≤ x / 2 * ∏ p ∈ U, kb p := by
    intro U hU
    have hUP : ∀ p ∈ U, p.Prime ∧ p ≠ 2 := fun p hp => hP p (mem_powerset.1 hU hp)
    rw [← sum_filter, sum_const, nsmul_eq_mul, prod_mul_distrib]
    have hc := k_card N U hUP
    have hpos : (0 : ℝ) < ∏ p ∈ U, (p : ℝ) :=
      prod_pos (fun p hp => by exact_mod_cast (hUP p hp).1.pos)
    have hc' : ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
      calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ)
          ≤ ((N / (2 * ∏ p ∈ U, p) : ℕ) : ℝ) := by exact_mod_cast hc
        _ ≤ (N : ℝ) / ((2 * ∏ p ∈ U, p : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
          push_cast
          gcongr
          exact Nat.floor_le hx
    have hb : 0 ≤ ∏ p ∈ U, kb p := prod_nonneg (fun p hp => kb_nonneg p (by
      have := (hUP p hp).1.two_le; have := (hUP p hp).2; omega))
    calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, kb p)
        ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, kb p) := by
          gcongr
      _ = x / 2 * ∏ p ∈ U, kb p := by field_simp
  calc ∑ U ∈ P.powerset, ∑ s ∈ E,
        (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * kb p) else 0)
      ≤ ∑ U ∈ P.powerset, x / 2 * ∏ p ∈ U, kb p := by
        gcongr with U hU; exact hterm U hU
    _ = (x / 2) * ∏ p ∈ P, (1 + kb p) := by
        rw [prod_one_add, mul_sum]
    _ ≤ (x / 2) * (37695 * (1 / (1 - 13 / 418))) := by gcongr; exact kb_prod P hP
    _ ≤ 19500 * x := by nlinarith

end P41

-- ===== TSum =====
/-! The small primes `Q` (the first 150 odd primes) and the weight sum `∑_{b<a} K(a-b)`. -/

open Finset Real

namespace P41
open Schnir
def Qc0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def Qc1 : List ℕ := [37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
def Qc2 : List ℕ := [79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
def Qc3 : List ℕ := [131, 137, 139, 149, 151, 157, 163, 167, 173, 179]
def Qc4 : List ℕ := [181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def Qc5 : List ℕ := [239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
def Qc6 : List ℕ := [293, 307, 311, 313, 317, 331, 337, 347, 349, 353]
def Qc7 : List ℕ := [359, 367, 373, 379, 383, 389, 397, 401, 409, 419]
def Qc8 : List ℕ := [421, 431, 433, 439, 443, 449, 457, 461, 463, 467]
def Qc9 : List ℕ := [479, 487, 491, 499, 503, 509, 521, 523, 541, 547]
def Qc10 : List ℕ := [557, 563, 569, 571, 577, 587, 593, 599, 601, 607]
def Qc11 : List ℕ := [613, 617, 619, 631, 641, 643, 647, 653, 659, 661]
def Qc12 : List ℕ := [673, 677, 683, 691, 701, 709, 719, 727, 733, 739]
def Qc13 : List ℕ := [743, 751, 757, 761, 769, 773, 787, 797, 809, 811]
def Qc14 : List ℕ := [821, 823, 827, 829, 839, 853, 857, 859, 863, 877]
def Qlist : List ℕ := Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14
theorem Qlist_nodup : Qlist.Nodup := by decide +kernel

def Qs : Finset ℕ := ⟨(Qlist : Multiset ℕ), Multiset.coe_nodup.2 Qlist_nodup⟩

theorem Qc0_prime : ∀ p ∈ Qc0, p.Prime := by
  simp only [Qc0, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc1_prime : ∀ p ∈ Qc1, p.Prime := by
  simp only [Qc1, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc2_prime : ∀ p ∈ Qc2, p.Prime := by
  simp only [Qc2, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc3_prime : ∀ p ∈ Qc3, p.Prime := by
  simp only [Qc3, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc4_prime : ∀ p ∈ Qc4, p.Prime := by
  simp only [Qc4, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc5_prime : ∀ p ∈ Qc5, p.Prime := by
  simp only [Qc5, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc6_prime : ∀ p ∈ Qc6, p.Prime := by
  simp only [Qc6, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc7_prime : ∀ p ∈ Qc7, p.Prime := by
  simp only [Qc7, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc8_prime : ∀ p ∈ Qc8, p.Prime := by
  simp only [Qc8, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc9_prime : ∀ p ∈ Qc9, p.Prime := by
  simp only [Qc9, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc10_prime : ∀ p ∈ Qc10, p.Prime := by
  simp only [Qc10, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc11_prime : ∀ p ∈ Qc11, p.Prime := by
  simp only [Qc11, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc12_prime : ∀ p ∈ Qc12, p.Prime := by
  simp only [Qc12, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc13_prime : ∀ p ∈ Qc13, p.Prime := by
  simp only [Qc13, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qc14_prime : ∀ p ∈ Qc14, p.Prime := by
  simp only [Qc14, List.forall_mem_cons, List.forall_mem_nil]
  norm_num

theorem Qlist_prime : ∀ p ∈ Qlist, p.Prime :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨Qc0_prime, Qc1_prime⟩, Qc2_prime⟩, Qc3_prime⟩, Qc4_prime⟩, Qc5_prime⟩, Qc6_prime⟩, Qc7_prime⟩, Qc8_prime⟩, Qc9_prime⟩, Qc10_prime⟩, Qc11_prime⟩, Qc12_prime⟩, Qc13_prime⟩, Qc14_prime⟩

theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 877 := by
  have hp' : p ∈ Qlist := Multiset.mem_coe.1 (Finset.mem_def.1 hp)
  refine ⟨Qlist_prime p hp', ?_, ?_⟩
  · have : ∀ q ∈ Qlist, q ≠ 2 := by decide +kernel
    exact this p hp'
  · have : ∀ q ∈ Qlist, q ≤ 877 := by decide +kernel
    exact this p hp'

theorem Qs_card : Qs.card = 150 := by decide +kernel

def Sset : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

def Wk (d : ℕ) : ℕ := ∏ p ∈ Sset, (if p ∣ d then p - 1 else p - 2)

def Dk : ℕ := ∏ p ∈ Sset, (p - 2)

theorem Sset_prime : ∀ p ∈ Sset, p.Prime ∧ 3 ≤ p := by
  intro p hp
  simp only [Sset, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

noncomputable def fK (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem one_le_fK (p : ℕ) (hp : 3 ≤ p) : 1 ≤ fK p := by
  unfold fK
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]; linarith

theorem fK_le_47 (p : ℕ) (hp : 47 ≤ p) : fK p ≤ 46 / 45 := by
  unfold fK
  have h : (47 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem fK_term (p d : ℕ) (hp : 3 ≤ p) :
    (if p ∣ d then fK p else 1) =
      (((if p ∣ d then p - 1 else p - 2 : ℕ) : ℝ) / (((p - 2 : ℕ)) : ℝ)) := by
  have hc1 : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hc2 : (((p - 2 : ℕ)) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hne : (p : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  split_ifs
  · unfold fK; push_cast [hc1, hc2]; rfl
  · push_cast [hc2]; rw [div_self hne]

theorem prod_S_eq (d : ℕ) :
    ∏ p ∈ Sset, (if p ∣ d then fK p else 1) = (Wk d : ℝ) / Dk := by
  rw [prod_congr rfl (fun p hp => fK_term p d (Sset_prime p hp).2), prod_div_distrib]
  unfold Wk Dk
  rw [Nat.cast_prod, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
theorem Kf_le_Wk (d : ℕ) (hd0 : 0 < d) (hdl : d < 2209) :
    Kf d ≤ 46 / 45 * (Wk d : ℝ) / Dk := by
  have hKf : Kf d = ∏ p ∈ d.primeFactors, (if 2 < p then fK p else 1) := rfl
  rw [hKf, ← prod_filter_mul_prod_filter_not d.primeFactors (fun p => p < 47)]
  have hsmall : d.primeFactors.filter (fun p => p < 47) = (insert 2 Sset).filter (fun p => p ∣ d) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, mem_insert]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hp47⟩
      refine ⟨?_, hpd⟩
      have := hpp.two_le
      interval_cases p <;> first | (left; rfl) | (right; decide) | (exfalso; norm_num at hpp)
    · rintro ⟨hp, hpd⟩
      rcases hp with rfl | hp
      · exact ⟨⟨Nat.prime_two, hpd, by omega⟩, by norm_num⟩
      · refine ⟨⟨(Sset_prime p hp).1, hpd, by omega⟩, ?_⟩
        simp only [Sset, mem_insert, mem_singleton] at hp
        omega
  have h2S : (2 : ℕ) ∉ Sset := by decide
  rw [hsmall, prod_filter, prod_insert h2S]
  have hS : ∏ p ∈ Sset, (if p ∣ d then (if 2 < p then fK p else 1) else 1) =
      ∏ p ∈ Sset, (if p ∣ d then fK p else 1) := by
    refine prod_congr rfl fun p hp => ?_
    have := (Sset_prime p hp).2
    rw [if_pos (show 2 < p by omega)]
  rw [hS, prod_S_eq]
  have h2 : (if 2 ∣ d then (if 2 < 2 then fK 2 else 1) else 1) = (1 : ℝ) := by simp
  rw [h2, one_mul]
  set Bf := d.primeFactors.filter (fun p => ¬ p < 47) with hBf
  have hcard : Bf.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hBf, mem_filter, Nat.mem_primeFactors] at ha hb
    by_contra hab
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha.1.1 hb.1.1).2 hab
    have hdiv : a * b ∣ d := hcop.mul_dvd_of_dvd_of_dvd ha.1.2.1 hb.1.2.1
    have hle := Nat.le_of_dvd hd0 hdiv
    have ha47 : 47 ≤ a := by omega
    have hb47 : 47 ≤ b := by omega
    have : 47 * 47 ≤ a * b := Nat.mul_le_mul ha47 hb47
    omega
  have hB : ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ 46 / 45 := by
    calc ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ∏ p ∈ Bf, (46 / 45 : ℝ) := by
          apply prod_le_prod
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; linarith [one_le_fK p (by omega)]
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; exact fK_le_47 p (by omega)
      _ = (46 / 45) ^ Bf.card := by rw [prod_const]
      _ ≤ (46 / 45) ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
      _ = 46 / 45 := pow_one _
  have hW : (0 : ℝ) ≤ (Wk d : ℝ) / Dk := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc ((Wk d : ℝ) / Dk) * ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ((Wk d : ℝ) / Dk) * (46 / 45) :=
        mul_le_mul_of_nonneg_left hB hW
    _ = 46 / 45 * (Wk d : ℝ) / Dk := by ring

def Wk2 (d : ℕ) : ℕ := (if d % 3 = 0 then 2 else 1) * (if d % 5 = 0 then 4 else 3) * (if d % 7 = 0 then 6 else 5) * (if d % 11 = 0 then 10 else 9) * (if d % 13 = 0 then 12 else 11) * (if d % 17 = 0 then 16 else 15) * (if d % 19 = 0 then 18 else 17) * (if d % 23 = 0 then 22 else 21) * (if d % 29 = 0 then 28 else 27) * (if d % 31 = 0 then 30 else 29) * (if d % 37 = 0 then 36 else 35) * (if d % 41 = 0 then 40 else 39) * (if d % 43 = 0 then 42 else 41)

theorem Wk_eq (d : ℕ) : Wk d = Wk2 d := by
  simp only [Wk, Sset, Wk2]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_singleton]
  simp only [Nat.dvd_iff_mod_eq_zero]
  norm_num only [mul_assoc]

def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then Wk2 (a - b) else 0).sum
theorem chunk0 : (Qc0.map rowW).sum ≤ 22334401544323050 := by decide +kernel
theorem chunk1 : (Qc1.map rowW).sum ≤ 81184428911190150 := by decide +kernel
theorem chunk2 : (Qc2.map rowW).sum ≤ 140965406992975950 := by decide +kernel
theorem chunk3 : (Qc3.map rowW).sum ≤ 201870775876366800 := by decide +kernel
theorem chunk4 : (Qc4.map rowW).sum ≤ 260284136341434975 := by decide +kernel
theorem chunk5 : (Qc5.map rowW).sum ≤ 323231843728747800 := by decide +kernel
theorem chunk6 : (Qc6.map rowW).sum ≤ 383210746492869540 := by decide +kernel
theorem chunk7 : (Qc7.map rowW).sum ≤ 441685524908464515 := by decide +kernel
theorem chunk8 : (Qc8.map rowW).sum ≤ 502604899649725320 := by decide +kernel
theorem chunk9 : (Qc9.map rowW).sum ≤ 563874701075903070 := by decide +kernel
theorem chunk10 : (Qc10.map rowW).sum ≤ 626127811285855725 := by decide +kernel
theorem chunk11 : (Qc11.map rowW).sum ≤ 683907388954790490 := by decide +kernel
theorem chunk12 : (Qc12.map rowW).sum ≤ 742991985680191380 := by decide +kernel
theorem chunk13 : (Qc13.map rowW).sum ≤ 805695899866849530 := by decide +kernel
theorem chunk14 : (Qc14.map rowW).sum ≤ 865807107315140655 := by decide +kernel

theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∑ a ∈ Qs, f a = (Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist : Multiset ℕ)) = _
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem Qlist_eq : Qlist = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 := rfl

theorem row_eq (a : ℕ) : (∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = rowW a := by
  rw [sum_Qs]
  simp only [Wk_eq, rowW]

theorem half_le : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) ≤ 6645777058624828950 := by
  have h1 : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = (Qlist.map rowW).sum := by
    rw [sum_Qs]
    simp only [row_eq]
  rw [h1, Qlist_eq]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (chunk0) chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14).trans_eq (by norm_num)

theorem Dk_eq : Dk = 348469040044125 := by
  simp [Dk, Sset]

theorem T_bound :
    ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤ 19496 := by
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤
      46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    intro a ha b hb
    obtain ⟨-, -, ha1⟩ := Qs_prop a ha
    split_ifs with hab
    · have := Kf_le_Wk (a - b) (by omega) (by omega)
      exact this.trans_eq (by ring)
    · simp
  have hD : (0 : ℝ) < Dk := by
    rw [Dk_eq]; norm_num
  have hk : 0 ≤ 46 / 45 / (Dk : ℝ) := div_nonneg (by norm_num) hD.le
  set H := (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0 : ℕ) with hH
  have hHle : (H : ℝ) ≤ 6645777058624828950 := by exact_mod_cast half_le
  have hcast : ((H : ℕ) : ℝ) = ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    rw [hH, Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
  calc ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0)
      ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, 46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
    _ = 46 / 45 / Dk * (H : ℝ) := by
        rw [hcast, mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
    _ ≤ 46 / 45 / Dk * (6645777058624828950 : ℝ) := mul_le_mul_of_nonneg_left hHle hk
    _ ≤ 19496 := by
        rw [Dk_eq]; norm_num

theorem pairs_card : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then 1 else 0 : ℕ) = 11175 := by
  decide +kernel

end P41

-- ===== RV =====
/-! Riesel–Vaughan small shifts: representations `s = a + q` with `a ∈ Q`, `q` an odd prime. -/

open Finset Real

namespace P41
open Schnir

/-- odd primes `≤ t`. -/
def oddP (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddP_card (M : ℕ) (hM : 2 ≤ M) : (oddP M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : oddP M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [oddP, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- `[s = a + q]` with `q` an odd prime. -/
noncomputable def ind (a s : ℕ) : ℕ := if a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2 then 1 else 0

/-- number of `a ∈ Q` with `s - a` an odd prime. -/
noncomputable def Rr (s : ℕ) : ℕ := #{a ∈ Qs | a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2}

theorem Rr_eq (s : ℕ) : Rr s = ∑ a ∈ Qs, ind a s := by
  rw [Rr, card_filter]; rfl

theorem ind_sq (a s : ℕ) : ind a s * ind a s = ind a s := by
  unfold ind; split_ifs <;> simp

theorem ind_mul (a b s : ℕ) : ind a s * ind b s =
    if (a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2) ∧ (b ≤ s ∧ (s - b).Prime ∧ s - b ≠ 2) then 1 else 0 := by
  unfold ind; rw [ite_zero_mul_ite_zero, one_mul]

/-- prime pairs `m, m + d` with `m + d ≤ x` (the count in Siebert's bound). -/
noncomputable def PPs (d x : ℕ) : ℕ := #{m ∈ range (x + 1) | m.Prime ∧ (m + d).Prime ∧ m + d ≤ x}

/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - 877`. -/
theorem sumR_lower (n : ℕ) (hn : 879 ≤ n) :
    150 * (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), Rr s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Qs, (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, ha877⟩ := Qs_prop a ha
    unfold ind
    rw [← card_filter]
    apply card_le_card_of_injOn (fun q => q + a)
    · intro q hq
      simp only [oddP, coe_filter, mem_range, Set.mem_ofPred_eq] at hq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, hq.2.1, hq.2.2⟩
    · intro q _ q' _ h
      simp only at h
      omega
  calc 150 * (oddP (n - 877)).card = ∑ _a ∈ Qs, (oddP (n - 877)).card := by
        rw [sum_const, Qs_card, smul_eq_mul]
    _ ≤ _ := sum_le_sum h

/-- a pair `b < a` of shifts hits a prime pair `(s - a, s - b)`. -/
theorem pair_le (a b n : ℕ) (hba : b < a) :
    ∑ s ∈ range (n + 1), ind a s * ind b s ≤ PPs (a - b) n := by
  simp_rw [ind_mul]
  rw [← card_filter, PPs]
  apply card_le_card_of_injOn (fun s => s - a)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    obtain ⟨hs, ⟨has, hpa, -⟩, ⟨hbs, hpb, -⟩⟩ := hs
    refine ⟨by omega, hpa, ?_, by omega⟩
    rwa [show s - a + (a - b) = s - b by omega]
  · intro s hs t ht h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs ht
    simp only at h
    omega

/-- pointwise square expansion. -/
theorem Rr_sq (s : ℕ) : Rr s ^ 2 = Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
  have hsplit : ∀ a b : ℕ, ind a s * ind b s = (if b < a then ind a s * ind b s else 0) +
      (if a = b then ind a s else 0) + (if a < b then ind a s * ind b s else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp [ind_sq]
    · simp [h, h.ne', not_lt.2 h.le]
  have hsym : (∑ a ∈ Qs, ∑ b ∈ Qs, if a < b then ind a s * ind b s else 0) =
      ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have hdiag : (∑ a ∈ Qs, ∑ b ∈ Qs, if a = b then ind a s else 0) = ∑ a ∈ Qs, ind a s :=
    sum_congr rfl fun a ha => by simp [ha]
  rw [Rr_eq, sq, sum_mul_sum]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b]
  simp only [sum_add_distrib]
  rw [hsym, hdiag]
  ring

/-- second moment: diagonal plus prime pairs. -/
theorem sumR2_le (n : ℕ) : ∑ s ∈ range (n + 1), Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 := by
  simp_rw [Rr_sq]
  rw [sum_add_distrib, ← mul_sum]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  split_ifs with h
  · exact pair_le a b n h
  · simp

theorem r_pos_of_Rr (s : ℕ) (h : Rr s ≠ 0) : 0 < r s := by
  rw [Rr] at h
  obtain ⟨a, ha⟩ := card_pos.1 (Nat.pos_of_ne_zero h)
  rw [mem_filter] at ha
  obtain ⟨haQ, has, hp, h2⟩ := ha
  obtain ⟨hap, ha2, -⟩ := Qs_prop a haQ
  unfold r
  exact card_pos.2 ⟨a, mem_filter.2 ⟨mem_range.2 (by omega), hap, ha2, hp, h2⟩⟩

/-- Cauchy–Schwarz. -/
theorem rv_cs (n : ℕ) : (∑ s ∈ range (n + 1), Rr s) ^ 2 ≤
    #{s ∈ range (n + 1) | 0 < r s} * ∑ s ∈ range (n + 1), Rr s ^ 2 := by
  set F := (range (n + 1)).filter (fun s => Rr s ≠ 0) with hF
  have h1 : ∑ s ∈ range (n + 1), Rr s = ∑ s ∈ F, Rr s := (sum_filter_ne_zero _).symm
  have h2 : ∑ s ∈ F, Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : #F ≤ #{s ∈ range (n + 1) | 0 < r s} := by
    apply card_le_card
    intro s hs
    rw [hF, mem_filter] at hs
    exact mem_filter.2 ⟨hs.1, r_pos_of_Rr s hs.2⟩
  rw [h1]
  calc (∑ s ∈ F, Rr s) ^ 2 ≤ #F * ∑ s ∈ F, Rr s ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul h3 h2


end P41

-- ===== RVPiece =====
/-! The analytic inequalities for one piece `La ≤ log n ≤ Lb` of the middle range. -/

open Finset Real

namespace P41
open Schnir

theorem exp99_ge (x : ℝ) (hx : 70 ≤ x) : (10 : ℝ) ^ 12 ≤ exp x := by
  have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
  have h : exp 70 = exp 2 ^ 35 := by rw [← exp_nat_mul]; norm_num
  calc (10 : ℝ) ^ 12 ≤ 3 ^ 35 := by norm_num
    _ ≤ exp 2 ^ 35 := pow_le_pow_left₀ (by norm_num) h3 35
    _ = exp 70 := h.symm
    _ ≤ exp x := exp_le_exp.2 hx

/-- first moment, from Chebyshev's `ψ(m) ≥ a m - 5 log m + 5` (`a ≥ 0.9212`). -/
theorem X_lower (n : ℕ) (Lb : ℝ) (hn : (10 : ℝ) ^ 12 ≤ n) (hLb : log n ≤ Lb) (hLb12 : Lb ≤ 12000) :
    150 * 0.9211 / Lb * n ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
  have hn879 : 879 ≤ n := by exact_mod_cast (show (879 : ℝ) ≤ n by linarith)
  set m := n - 877 with hm
  have hmR : (m : ℝ) = n - 877 := by rw [hm, Nat.cast_sub (by omega)]; norm_num
  have hX := sumR_lower n hn879
  have hP := oddP_card m (by omega)
  have hpsi1 := Chebyshev.psi_le_primeCounting_mul_log m
  have hpsi2 := Chebyshev.psi_lower (m : ℝ) (by rw [hmR]; linarith)
  have ha := Chebyshev.a_bound.1
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  have hlogm : log m ≤ log n := log_le_log hm0 (by rw [hmR]; linarith)
  have hlogm0 : 0 < log (m : ℝ) := log_pos (by rw [hmR]; linarith)
  have hc : ((oddP m).card : ℝ) + 1 = Nat.primeCounting m := by exact_mod_cast hP
  have e1 : ((oddP m).card : ℝ) * log m = (Nat.primeCounting m : ℝ) * log m - log m := by
    rw [← hc]; ring
  have key : Chebyshev.a * (m : ℝ) - 6 * log m + 5 ≤ ((oddP m).card : ℝ) * log m := by
    rw [e1]; linarith
  have hcard0 : (0 : ℝ) ≤ (oddP m).card := Nat.cast_nonneg _
  have hk2 : ((oddP m).card : ℝ) * log m ≤ ((oddP m).card : ℝ) * Lb :=
    mul_le_mul_of_nonneg_left (hlogm.trans hLb) hcard0
  have hlogm12 : log (m : ℝ) ≤ 12000 := hlogm.trans (hLb.trans hLb12)
  have hma : Chebyshev.a * (m : ℝ) ≥ 0.9212 * m := mul_le_mul_of_nonneg_right ha hm0.le
  have hmain : 0.9211 * (n : ℝ) ≤ ((oddP m).card : ℝ) * Lb := by
    linarith
  have hLbpos : 0 < Lb := lt_of_lt_of_le (log_pos (by linarith)) hLb
  have hXc : (150 : ℝ) * (oddP m).card ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
    exact_mod_cast hX
  rw [div_mul_eq_mul_div, div_le_iff₀ hLbpos]
  have := mul_le_mul_of_nonneg_right hXc hLbpos.le
  linarith

/-- Siebert's bound for one shift. -/
theorem PPs_le (d n : ℕ) (hn : 2 ≤ n) (hd0 : 0 < d) (hd2 : 2 ∣ d) :
    (PPs d n : ℝ) ≤ 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 * Kf d := by
  have h := TaoFivePrimes.siebert_prime_pair_bound n d hn hd0 hd2
  have e : (PPs d n : ℝ) = ∑ m ∈ range (n + 1),
      if Nat.Prime m ∧ Nat.Prime (m + d) ∧ m + d ≤ n then (1 : ℝ) else 0 := by
    rw [PPs, Finset.natCast_card_filter]
  rw [e]
  exact h

/-- the off-diagonal (prime pair) part of the second moment. -/
theorem off_le (n : ℕ) (La : ℝ) (hLa : 30 ≤ La) (h1 : La ≤ log n) :
    ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      n * (16 * 1.3217 * 19496 / La ^ 2) := by
  obtain ⟨-, hCup, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  have hC0 : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
    obtain ⟨h, -⟩ := PrimePairSieve.sieve_constants_certificate; linarith
  have hL : 30 ≤ log (n : ℝ) := hLa.trans h1
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hL; simp at hL; linarith
    · exact_mod_cast h
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : (n : ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
    have := log_le_log hnpos this
    rw [log_one] at this; linarith
  set w := 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * (if b < a then Kf (a - b) else 0) := by
    intro a ha b hb
    obtain ⟨hap, ha2, -⟩ := Qs_prop a ha
    obtain ⟨hbp, hb2, -⟩ := Qs_prop b hb
    split_ifs with hab
    · have hao := hap.odd_of_ne_two ha2
      have hbo := hbp.odd_of_ne_two hb2
      have hev : 2 ∣ a - b := by
        obtain ⟨i, hi⟩ := hao; obtain ⟨j, hj⟩ := hbo
        exact ⟨i - j, by omega⟩
      exact PPs_le (a - b) n hn2 (by omega) hev
    · simp
  have hsum : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * 19496 := by
    have hcast : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) =
        ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
    rw [hcast]
    calc ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ)
        ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, w * (if b < a then Kf (a - b) else 0) :=
          sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
      _ = w * ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) := by
          rw [mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
      _ ≤ w * 19496 := mul_le_mul_of_nonneg_left T_bound hw0
  have hwle : w ≤ 8 * 1.3217 * n / La ^ 2 := by
    rw [hw]
    have hLa2 : La ^ 2 ≤ (log n) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    calc 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 ≤ 8 * 1.3217 * n / (log n) ^ 2 := by
          gcongr
      _ ≤ 8 * 1.3217 * n / La ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hLa2
  push_cast at hsum ⊢
  have : 2 * (w * 19496) ≤ n * (16 * 1.3217 * 19496 / La ^ 2) := by
    have e : (n : ℝ) * (16 * 1.3217 * 19496 / La ^ 2) = 2 * (8 * 1.3217 * n / La ^ 2 * 19496) := by ring
    rw [e]; nlinarith
  linarith

/-- one piece of the middle range: `#{s ≤ n : r(s) > 0} ≥ n / 39`. -/
theorem rv_piece (n : ℕ) (La Lb : ℝ) (hLa : 30 ≤ La) (hLb12 : Lb ≤ 12000)
    (h1 : La ≤ log n) (h2 : log n ≤ Lb) (hxb : 1 / 78 ≤ 150 * 0.9211 / Lb)
    (hnum : 150 * 0.9211 / Lb + 16 * 1.3217 * 19496 / La ^ 2 ≤ 39 * (150 * 0.9211 / Lb) ^ 2) :
    (n : ℝ) / 39 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  have hn12 : (10 : ℝ) ^ 12 ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at h1; simp at h1; linarith
      · exact_mod_cast h
    rw [← exp_log hnpos]
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have : (10 : ℝ) ^ 12 ≤ exp 30 := by
      have e : exp 30 = exp 1 ^ 30 := by rw [← exp_nat_mul]; norm_num
      rw [e]
      calc (10 : ℝ) ^ 12 ≤ 2.7 ^ 30 := by norm_num
        _ ≤ exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) h3 30
    exact this.trans (exp_le_exp.2 (by linarith))
  set x := 150 * 0.9211 / Lb with hx
  set k := 16 * 1.3217 * 19496 / La ^ 2 with hk
  have hX := X_lower n Lb hn12 h2 hLb12
  have hoff := off_le n La hLa h1
  have hcs := rv_cs n
  have h2m := sumR2_le n
  set X := ∑ s ∈ range (n + 1), Rr s with hXdef
  set off := 2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 with hoffdef
  set cnt := #{s ∈ range (n + 1) | 0 < r s} with hcnt
  have hcsN : X ^ 2 ≤ cnt * (X + off) := hcs.trans (Nat.mul_le_mul_left _ h2m)
  have hcsR : (X : ℝ) ^ 2 ≤ cnt * (X + off) := by exact_mod_cast hcsN
  have hX' : (n : ℝ) * x ≤ X := by rw [hx, mul_comm]; exact hX
  have hoff' : (off : ℝ) ≤ n * k := by rw [hk]; exact hoff
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ cnt := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by linarith
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < (X : ℝ) := lt_of_lt_of_le (mul_pos hnpos hxpos) hX'
  have hnk : 0 ≤ (n : ℝ) * k := mul_nonneg hn0 hk0
  have h3 : (cnt : ℝ) * (X + off) ≤ cnt * (X + n * k) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have h4 : (cnt : ℝ) * (X + n * k) < n / 39 * (X + n * k) :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have p1 : 0 ≤ ((X : ℝ) - n * x) * (X + n * x - n / 39) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (n : ℝ) * (2 * x - 1 / 39) := mul_nonneg hn0 (by linarith)
    linarith
  have p2 : 0 ≤ (n : ℝ) ^ 2 * (39 * x ^ 2 - x - k) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (X : ℝ) ^ 2 - n / 39 * (X + n * k) =
      ((X : ℝ) - n * x) * (X + n * x - n / 39) + (n : ℝ) ^ 2 * (39 * x ^ 2 - x - k) / 39 := by
    ring
  linarith

end P41

-- ===== RVRange =====
/-! The middle range `30 ≤ log n ≤ 2000`, split into pieces. -/

open Finset Real

namespace P41
open Schnir

theorem rv_range (n : ℕ) (h1 : 30 ≤ log n) (h2 : log n ≤ 2000) :
    (n : ℝ) / 39 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  rcases le_or_gt (log (n : ℝ)) 40 with hb0 | ha0
  · exact rv_piece n 30 40 (by norm_num) (by norm_num) h1 hb0 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 53 with hb1 | ha1
  · exact rv_piece n 40 53 (by norm_num) (by norm_num) ha0.le hb1 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 70 with hb2 | ha2
  · exact rv_piece n 53 70 (by norm_num) (by norm_num) ha1.le hb2 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 93 with hb3 | ha3
  · exact rv_piece n 70 93 (by norm_num) (by norm_num) ha2.le hb3 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 123 with hb4 | ha4
  · exact rv_piece n 93 123 (by norm_num) (by norm_num) ha3.le hb4 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 162 with hb5 | ha5
  · exact rv_piece n 123 162 (by norm_num) (by norm_num) ha4.le hb5 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 213 with hb6 | ha6
  · exact rv_piece n 162 213 (by norm_num) (by norm_num) ha5.le hb6 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 278 with hb7 | ha7
  · exact rv_piece n 213 278 (by norm_num) (by norm_num) ha6.le hb7 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 360 with hb8 | ha8
  · exact rv_piece n 278 360 (by norm_num) (by norm_num) ha7.le hb8 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 462 with hb9 | ha9
  · exact rv_piece n 360 462 (by norm_num) (by norm_num) ha8.le hb9 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 586 with hb10 | ha10
  · exact rv_piece n 462 586 (by norm_num) (by norm_num) ha9.le hb10 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 732 with hb11 | ha11
  · exact rv_piece n 586 732 (by norm_num) (by norm_num) ha10.le hb11 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 897 with hb12 | ha12
  · exact rv_piece n 732 897 (by norm_num) (by norm_num) ha11.le hb12 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1078 with hb13 | ha13
  · exact rv_piece n 897 1078 (by norm_num) (by norm_num) ha12.le hb13 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1266 with hb14 | ha14
  · exact rv_piece n 1078 1266 (by norm_num) (by norm_num) ha13.le hb14 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1453 with hb15 | ha15
  · exact rv_piece n 1266 1453 (by norm_num) (by norm_num) ha14.le hb15 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1630 with hb16 | ha16
  · exact rv_piece n 1453 1630 (by norm_num) (by norm_num) ha15.le hb16 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1789 with hb17 | ha17
  · exact rv_piece n 1630 1789 (by norm_num) (by norm_num) ha16.le hb17 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1926 with hb18 | ha18
  · exact rv_piece n 1789 1926 (by norm_num) (by norm_num) ha17.le hb18 (by norm_num) (by norm_num)
  exact rv_piece n 1926 2000 (by norm_num) (by norm_num) ha18.le h2 (by norm_num) (by norm_num)

end P41

-- ===== Large =====
/-! Large range `n ≥ e^2000`: pointwise Goldbach–Siebert bound with the sharp weight `K(s)`, weighted first moment, and Hölder with the twelfth moment of `K`. -/

open Finset Real

namespace P41
open Schnir

theorem log_le_two_sqrt (y : ℝ) (hy : 0 < y) : log y ≤ 2 * √y := by
  have h := log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
  rw [Real.log_sqrt hy.le] at h
  linarith

/-- `#(odd primes ≤ t) ≥ 0.9211 (t - 10^6) / log n` for `t ≤ n`. -/
theorem Q_lower (n t : ℕ) (hn : 10 ^ 6 ≤ n) (ht : t ≤ n) :
    0.9211 / log n * ((t : ℝ) - 10 ^ 6) ≤ (s6P t).card := by
  have hn' : (10 : ℝ) ^ 6 ≤ n := by exact_mod_cast hn
  have hlogn : 0 < log n := log_pos (by linarith)
  by_cases h : t < 10 ^ 6
  · have : ((t : ℝ) - 10 ^ 6) ≤ 0 := by
      have : (t : ℝ) < 10 ^ 6 := by exact_mod_cast h
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) this).trans (Nat.cast_nonneg _)
  · push Not at h
    have ht' : (10 : ℝ) ^ 6 ≤ t := by exact_mod_cast h
    have hc := s6_card_P t (by omega)
    have hc' : ((s6P t).card : ℝ) + 1 = Nat.primeCounting t := by exact_mod_cast hc
    have hpsi1 := Chebyshev.psi_le_primeCounting_mul_log t
    have hpsi2 := Chebyshev.psi_lower (t : ℝ) (by linarith)
    have ha := Chebyshev.a_bound.1
    have hlogt : 0 < log (t : ℝ) := log_pos (by linarith)
    have hle : log (t : ℝ) ≤ log n := log_le_log (by linarith) (by exact_mod_cast ht)
    have e1 : ((s6P t).card : ℝ) * log t = (Nat.primeCounting t : ℝ) * log t - log t := by
      rw [← hc']; ring
    have hta : Chebyshev.a * (t : ℝ) ≥ 0.9212 * t := mul_le_mul_of_nonneg_right ha (by linarith)
    -- `6 log t ≤ 12 √t ≤ 0.0001 t + 360000`
    set q := √((t : ℝ) + 1) with hq
    have hq2 : q ^ 2 = (t : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hlq := log_le_two_sqrt ((t : ℝ) + 1) (by linarith)
    have hlt1 : log (t : ℝ) ≤ log ((t : ℝ) + 1) := log_le_log (by linarith) (by linarith)
    have hsq : 12 * q ≤ 0.0001 * (q ^ 2 - 1) + 360001 := by nlinarith [sq_nonneg (q - 60000)]
    have key : 0.9211 * ((t : ℝ) - 10 ^ 6) ≤ ((s6P t).card : ℝ) * log t := by
      rw [e1]; nlinarith
    have hcard0 : (0 : ℝ) ≤ (s6P t).card := Nat.cast_nonneg _
    have hk2 : ((s6P t).card : ℝ) * log t ≤ ((s6P t).card : ℝ) * log n :=
      mul_le_mul_of_nonneg_left hle hcard0
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogn]
    linarith

lemma gauss6 (K : ℕ) : ∑ t ∈ range K, ((t : ℝ) - 10 ^ 6) = (K : ℝ) * (K - 1) / 2 - 10 ^ 6 * K := by
  induction K with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The lower function `L(t) = 0.9211² (t - 10^6)(t - 3000001) / (2 (log t)^2)`. -/
noncomputable def Lf (t : ℝ) : ℝ := 0.9211 ^ 2 * (t - 10 ^ 6) * (t - 3000001) / (2 * (log t) ^ 2)

/-- Triangle first moment: `∑_{s ≤ n} r(s) ≥ L(n)` for `n ≥ 10^6`. -/
theorem first_moment (n : ℕ) (hn : 10 ^ 6 ≤ n) :
    Lf n ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
  set K := n - 10 ^ 6 with hKdef
  have hn' : (10 : ℝ) ^ 6 ≤ n := by exact_mod_cast hn
  have hlogn : 0 < log n := log_pos (by linarith)
  set c := 0.9211 / log n with hc
  have hc0 : 0 ≤ c := by positivity
  have hK : (K : ℝ) = n - 10 ^ 6 := by rw [hKdef, Nat.cast_sub hn]; push_cast; ring
  have hstep1 : ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]; exact_mod_cast s6_pairs n K (by omega)
  have hstep2 : c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) ≤ ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simp only [s6P, Finset.mem_filter, Finset.mem_range] at hp
    have := Q_lower n (n - p) hn (by omega)
    have e : ((n - p : ℕ) : ℝ) - 10 ^ 6 = ((K - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hK]; ring
    rw [e] at this; exact this
  have hstep3 : ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) = ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, s6_swap]
  have hstep4 : c * ∑ t ∈ range K, ((t : ℝ) - 10 ^ 6) ≤ ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_range] at ht
    exact Q_lower n t hn (by omega)
  rw [gauss6] at hstep4
  have hfin : Lf n = c * (c * ((K : ℝ) * (K - 1) / 2 - 10 ^ 6 * K)) := by
    rw [Lf, hc, hK]; field_simp; ring
  rw [hfin]
  calc c * (c * ((K : ℝ) * (K - 1) / 2 - 10 ^ 6 * K))
      ≤ c * ∑ t ∈ range K, ((s6P t).card : ℝ) := mul_le_mul_of_nonneg_left hstep4 hc0
    _ = c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) := by rw [hstep3]
    _ ≤ _ := hstep2.trans hstep1

/-- `exp t ≥ (Σ_{i<8} (t/16)^i/i!)^16`, for checking `log Lb ≤ lb`. -/
theorem exp_ge_poly (t : ℝ) (ht : 0 ≤ t) :
    (1 + t / 16 + (t / 16) ^ 2 / 2 + (t / 16) ^ 3 / 6 + (t / 16) ^ 4 / 24 + (t / 16) ^ 5 / 120 +
      (t / 16) ^ 6 / 720 + (t / 16) ^ 7 / 5040) ^ 16 ≤ exp t := by
  have h := sum_le_exp_of_nonneg (x := t / 16) (by positivity) 8
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, pow_zero, pow_one] at h
  norm_num at h
  have e : exp t = exp (t / 16) ^ 16 := by rw [← exp_nat_mul]; congr 1; ring
  rw [e]
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- Per-term bound: `(L(t) - L(t-1)) · (log t)^2 / t ≥ 0.8478` for `t ≥ e^1960`. -/
lemma term_lower (t : ℝ) (ht : exp 1960 ≤ t) :
    8478 / 10000 ≤ (Lf t - Lf (t - 1)) * (log t ^ 2 / t) := by
  have hbig : (10 : ℝ) ^ 12 ≤ t := (exp99_ge 1960 (by norm_num)).trans ht
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  set u := log t with hu_def
  set v := log (t - 1) with hv_def
  have hu : 1960 ≤ u := by
    have := log_le_log (exp_pos 1960) ht
    rwa [log_exp] at this
  have hvu : v ≤ u := log_le_log ht1 (by linarith)
  have huv : u - v ≤ 1 / (t - 1) := by
    have h := log_le_sub_one_of_pos (show 0 < t / (t - 1) by positivity)
    rw [log_div (by linarith) ht1.ne'] at h
    have : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  have hinv : 1 / (t - 1) ≤ 1 := by
    rw [div_le_one ht1]; linarith
  have hv : 1959 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  have hsq : u ^ 2 - v ^ 2 ≤ 2 * u / (t - 1) := by
    have : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [this]
    calc (u - v) * (u + v) ≤ 1 / (t - 1) * (u + v) :=
          mul_le_mul_of_nonneg_right huv (by linarith)
      _ ≤ 1 / (t - 1) * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * u / (t - 1) := by ring
  have huv2 : u / v ^ 2 ≤ 1 / 1900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hratio : u ^ 2 / v ^ 2 ≤ 1 + 2 / 1900 / (t - 1) := by
    have e : u ^ 2 / v ^ 2 = 1 + (u ^ 2 - v ^ 2) / v ^ 2 := by field_simp; ring
    rw [e]
    have : (u ^ 2 - v ^ 2) / v ^ 2 ≤ 2 * u / (t - 1) / v ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e2 : 2 * u / (t - 1) / v ^ 2 = 2 * (u / v ^ 2) / (t - 1) := by field_simp
    have : 2 * (u / v ^ 2) / (t - 1) ≤ 2 * (1 / 1900) / (t - 1) :=
      div_le_div_of_nonneg_right (by linarith) ht1.le
    have e3 : 2 * (1 / 1900) / (t - 1) = 2 / 1900 / (t - 1) := by ring
    linarith
  set g := (t - 1 - 10 ^ 6) * (t - 1 - 3000001) with hg
  have hg0 : 0 ≤ g := by rw [hg]; apply mul_nonneg <;> linarith
  have hgle : g ≤ (t - 1) ^ 2 := by rw [hg]; nlinarith
  have hexp : (Lf t - Lf (t - 1)) * (u ^ 2 / t)
      = 0.9211 ^ 2 / 2 * ((t - 10 ^ 6) * (t - 3000001) - g * (u ^ 2 / v ^ 2)) / t := by
    rw [Lf, Lf, ← hu_def, ← hv_def, hg]
    field_simp
  rw [hexp]
  have hgr : g * (u ^ 2 / v ^ 2) ≤ g + 2 / 1900 * (t - 1) := by
    calc g * (u ^ 2 / v ^ 2) ≤ g * (1 + 2 / 1900 / (t - 1)) := mul_le_mul_of_nonneg_left hratio hg0
      _ = g + 2 / 1900 * (g / (t - 1)) := by ring
      _ ≤ g + 2 / 1900 * (t - 1) := by
        have : g / (t - 1) ≤ t - 1 := by
          rw [div_le_iff₀ ht1]; nlinarith
        linarith
  rw [le_div_iff₀ (by linarith)]
  have e4 : (t - 10 ^ 6) * (t - 3000001) = g + 2 * t - 4000002 := by rw [hg]; ring
  rw [e4]
  nlinarith


set_option maxHeartbeats 2000000 in
/-- Sieve bound above `e^1960`: `r(s) ≤ 10.5737 K(s) s / log² s`. -/
theorem pointwise (s : ℕ) (hs : Even s) (hbig : exp 1960 ≤ s) :
    (r s : ℝ) ≤ 105737 / 10000 * Kf s * s / (log s) ^ 2 := by
  have hE : (10 : ℝ) ^ 12 ≤ exp 1960 := exp99_ge 1960 (by norm_num)
  have hs12 : (10 : ℝ) ^ 12 ≤ s := hE.trans hbig
  have hspos : (0 : ℝ) < s := by linarith
  have hs1 : 25599 ≤ s := by
    have : (25599 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hg := gs_main s hs hs1
  have hC := (PrimePairSieve.sieve_constants_certificate).2.1
  have hC0 : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
    have := (PrimePairSieve.sieve_constants_certificate).1; linarith
  have hK := one_le_Kf s
  set K := Kf s
  set L := log (s : ℝ) with hLdef
  have hL : 1960 ≤ L := by
    have := log_le_log (exp_pos 1960) hbig
    rwa [log_exp] at this
  have hL0 : 0 < L := by linarith
  have hL1 : L ≤ log ((s : ℝ) + 1) := log_le_log hspos (by linarith)
  have hA : 8 * TaoFivePrimes.twinPrimeConstant * K * ((s : ℝ) + 1) / (log ((s : ℝ) + 1)) ^ 2
      ≤ 105736 / 10000 * K * ((s : ℝ) + 1) / L ^ 2 := by
    have h1 : 8 * TaoFivePrimes.twinPrimeConstant * K * ((s : ℝ) + 1)
        ≤ 105736 / 10000 * K * ((s : ℝ) + 1) := by
      have : 8 * TaoFivePrimes.twinPrimeConstant ≤ 105736 / 10000 := by linarith
      have hKs : 0 ≤ K * ((s : ℝ) + 1) := by positivity
      nlinarith
    have h2 : L ^ 2 ≤ (log ((s : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hL0.le hL1 2
    calc _ ≤ 105736 / 10000 * K * ((s : ℝ) + 1) / (log ((s : ℝ) + 1)) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  set q := √(s : ℝ) with hq
  have hq2 : q ^ 2 = s := Real.sq_sqrt hspos.le
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hsq1 : √((s : ℝ) + 1) ≤ 2 * q := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · positivity
  have hqexp : q = exp (L / 2) := by
    rw [exp_half, hLdef, exp_log hspos]
  have h5 : L ^ 5 / 3840 ≤ q := by
    rw [hqexp]
    have := pow_div_factorial_le_exp (x := L / 2) (by linarith) 5
    norm_num [Nat.factorial] at this
    linarith
  have hL3 : (10 : ℝ) ^ 9 ≤ L ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hL 3]
  have hqL : 100000 * L ^ 2 ≤ q := by
    have : L ^ 5 = L ^ 3 * L ^ 2 := by ring
    have hL2 : 0 ≤ L ^ 2 := by positivity
    nlinarith
  have hq1 : 1 ≤ q := by nlinarith
  -- `10.5736 K + (q + 2) L² ≤ 0.0001 K q²`
  have hkey : 105736 / 10000 * K + (q + 2) * L ^ 2 ≤ 1 / 10000 * K * q ^ 2 := by
    have hK0 : 0 ≤ K := by linarith
    have hq3 : 3 * L ^ 2 ≤ q / 30000 := by nlinarith
    have hqq : 300000 ≤ q := by nlinarith
    have a1 : 105736 / 10000 * K ≤ 1 / 20000 * K * q ^ 2 := by
      have : (105736 / 10000 : ℝ) ≤ 1 / 20000 * q ^ 2 := by nlinarith
      nlinarith
    have a2 : (q + 2) * L ^ 2 ≤ 1 / 20000 * K * q ^ 2 := by
      have : (q + 2) * L ^ 2 ≤ q * (3 * L ^ 2) := by nlinarith
      have : q * (3 * L ^ 2) ≤ q * (q / 30000) := mul_le_mul_of_nonneg_left hq3 hq0
      have : q ^ 2 ≤ K * q ^ 2 := by nlinarith
      nlinarith
    linarith
  have hfin : 105736 / 10000 * K * ((s : ℝ) + 1) / L ^ 2 + √((s : ℝ) + 1) / 2 + 2
      ≤ 105737 / 10000 * K * s / L ^ 2 := by
    have hL2 : 0 < L ^ 2 := by positivity
    have e : 105737 / 10000 * K * s / L ^ 2 - 105736 / 10000 * K * ((s : ℝ) + 1) / L ^ 2
        - (q + 2) = (1 / 10000 * K * q ^ 2 - 105736 / 10000 * K - (q + 2) * L ^ 2) / L ^ 2 := by
      rw [hq2]; field_simp; ring
    have : 0 ≤ (1 / 10000 * K * q ^ 2 - 105736 / 10000 * K - (q + 2) * L ^ 2) / L ^ 2 :=
      div_nonneg (by linarith only [hkey]) hL2.le
    have h7 : √((s : ℝ) + 1) / 2 + 2 ≤ q + 2 := by linarith only [hsq1, hq0]
    linarith only [h7, this, e]
  linarith only [hg, hA, hfin]

/-- Weighted first moment: `W(n) ≥ 0.8477 n` for `n ≥ e^2000`. -/
theorem W_lower (n : ℕ) (hn : exp 2000 ≤ n) :
    8477 / 10000 * (n : ℝ) ≤ ∑ s ∈ Ioc ⌊exp 1960⌋₊ n, (r s : ℝ) * (log s ^ 2 / s) := by
  set n0 := ⌊exp 1960⌋₊ with hn0def
  have hE : (10 : ℝ) ^ 12 ≤ exp 1960 := exp99_ge 1960 (by norm_num)
  have hE3 : (10 : ℝ) ^ 17 ≤ exp 40 := (exp_ge_poly 40 (by norm_num)).trans' (by norm_num)
  have hn0 : (n0 : ℝ) ≤ exp 1960 := Nat.floor_le (exp_pos _).le
  have hn0' : exp 1960 < n0 + 1 := Nat.lt_floor_add_one _
  have hexp2 : exp 2000 = exp 1960 * exp 40 := by
    rw [← exp_add]; norm_num
  have hn1 : (n : ℝ) ≥ 10 ^ 17 * exp 1960 := by
    have := mul_le_mul_of_nonneg_left hE3 (exp_pos 1960).le
    linarith
  have hnn0 : n0 ≤ n := by
    have : (n0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hbig : ∀ k : ℕ, n0 < k → exp 1960 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have habel := s6_abel (fun s => (r s : ℝ)) (fun s => log s ^ 2 / s) (fun s => Lf s) n0
    (by
      intro k hk
      have := s6_w_anti k ((exp_le_exp.2 (by norm_num : (130 : ℝ) ≤ 1960)).trans (hbig k hk))
      push_cast; exact this)
    (by
      intro k hk
      have h1 := hbig k hk
      have : ((10 ^ 6 : ℕ) : ℝ) ≤ k := by push_cast; linarith
      exact first_moment k (by exact_mod_cast this))
    n hnn0
  -- (i) main sum
  have hi : 8478 / 10000 * ((n : ℝ) - n0) ≤
      ∑ s ∈ Ioc n0 n, (Lf s - Lf ((s - 1 : ℕ) : ℝ)) * (log s ^ 2 / s) := by
    have hcard : ((Ioc n0 n).card : ℝ) = (n : ℝ) - n0 := by
      rw [Nat.card_Ioc, Nat.cast_sub hnn0]
    rw [← hcard, mul_comm, ← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro s hs
    simp only [Finset.mem_Ioc] at hs
    have h1 := hbig s hs.1
    have : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    exact term_lower s h1
  -- (ii) the end term is nonnegative
  have hii : 0 ≤ (∑ s ∈ range (n + 1), (r s : ℝ) - Lf n) * (log ((n + 1 : ℕ) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
    apply mul_nonneg
    · have h1 := hbig n (by
        by_contra h; push Not at h
        have : n = n0 := le_antisymm h hnn0
        rw [this] at hn1; linarith)
      have : ((10 ^ 6 : ℕ) : ℝ) ≤ n := by push_cast; linarith
      have := first_moment n (by exact_mod_cast this)
      linarith
    · positivity
  -- (iii) the start term is small
  have hiii : (∑ s ∈ range (n0 + 1), (r s : ℝ) - Lf n0) * (log ((n0 + 1 : ℕ) : ℝ) ^ 2 / ((n0 + 1 : ℕ) : ℝ))
      ≤ 2 * 1961 ^ 2 * exp 1960 := by
    have hn0big : (3000001 : ℝ) ≤ n0 := by
      have : (3000002 : ℝ) ≤ exp 1960 := by linarith
      have : (3000002 : ℝ) < n0 + 1 := by linarith
      have : (3000002 : ℕ) < n0 + 1 := by exact_mod_cast this
      exact_mod_cast (show 3000001 ≤ n0 by omega)
    have hL0 : 0 ≤ Lf n0 := by
      unfold Lf
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    have hM0 : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ ((n0 : ℝ) + 1) ^ 2 := by
      have : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ (range (n0 + 1)).card • ((n0 : ℝ) + 1) := by
        apply Finset.sum_le_card_nsmul
        intro s hs
        simp only [Finset.mem_range] at hs
        have : r s ≤ n0 + 1 := (s6_r_le s).trans (by omega)
        exact_mod_cast this
      rw [Finset.card_range, nsmul_eq_mul] at this
      push_cast at this; nlinarith
    push_cast
    set m := (n0 : ℝ) + 1 with hm
    have hm0 : 0 < m := by linarith
    have hlogm : log m ≤ 1961 := by
      rw [log_le_iff_le_exp hm0]
      have : exp 1961 = exp 1960 * exp 1 := by rw [← exp_add]; norm_num
      have h2 : (2 : ℝ) ≤ exp 1 := by have := add_one_le_exp (1 : ℝ); linarith
      nlinarith
    have hlogm0 : 0 ≤ log m := log_nonneg (by linarith)
    have hw0 : 0 ≤ log m ^ 2 / m := by positivity
    calc (∑ s ∈ range (n0 + 1), (r s : ℝ) - Lf n0) * (log m ^ 2 / m)
        ≤ m ^ 2 * (log m ^ 2 / m) := mul_le_mul_of_nonneg_right (by linarith) hw0
      _ = m * log m ^ 2 := by field_simp
      _ ≤ (2 * exp 1960) * 1961 ^ 2 := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ hlogm0 hlogm 2) (by positivity) (by positivity)
      _ = 2 * 1961 ^ 2 * exp 1960 := by ring
  push_cast at hii hiii habel
  linarith


/-- Support bound: `R(n) ≥ n / 39` for `n ≥ e^2000`. -/
theorem R_large (n : ℕ) (hn : exp 2000 ≤ n) :
    (n : ℝ) / 39 ≤ (((range (n + 1)).filter (fun s => 0 < r s)).card : ℝ) := by
  set n0 := ⌊exp 1960⌋₊ with hn0def
  have hn0' : exp 1960 < n0 + 1 := Nat.lt_floor_add_one _
  have hbig : ∀ k : ℕ, n0 < k → exp 1960 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hW := W_lower n hn
  set F := (Ioc n0 n).filter (fun s => 0 < r s) with hF
  set R := (range (n + 1)).filter (fun s => 0 < r s) with hR
  have hWF : ∑ s ∈ Ioc n0 n, (r s : ℝ) * (log s ^ 2 / s)
      = ∑ s ∈ F, (r s : ℝ) * (log s ^ 2 / s) := by
    rw [hF, Finset.sum_filter_of_ne]
    intro s _ h
    by_contra h'
    push Not at h'
    have : r s = 0 := by omega
    simp [this] at h
  have hH := pow_sum_le_card_mul_sum_pow (s := F) (f := fun s => (r s : ℝ) * (log s ^ 2 / s))
    (fun s _ => by positivity) 11
  have hterm : ∀ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 12 ≤ (105737 / 10000) ^ 12 * Kf s ^ 12 := by
    intro s hs
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
    have heven : Even s := by
      by_contra h
      have := s6_r_odd s h
      omega
    have h1 := hbig s hs.1.1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (exp_pos _) h1
    have hlog : 0 < log s := log_pos (by nlinarith [add_one_le_exp (1960 : ℝ)])
    have hpb := pointwise s heven h1
    have hup : (r s : ℝ) * (log s ^ 2 / s) ≤ 105737 / 10000 * Kf s := by
      have hw : 0 < log s ^ 2 / s := by positivity
      calc (r s : ℝ) * (log s ^ 2 / s) ≤ 105737 / 10000 * Kf s * s / log s ^ 2 * (log s ^ 2 / s) :=
            mul_le_mul_of_nonneg_right hpb hw.le
        _ = 105737 / 10000 * Kf s := by field_simp
    have hlo : 0 ≤ (r s : ℝ) * (log s ^ 2 / s) := by positivity
    calc ((r s : ℝ) * (log s ^ 2 / s)) ^ 12 ≤ (105737 / 10000 * Kf s) ^ 12 := pow_le_pow_left₀ hlo hup 12
      _ = (105737 / 10000) ^ 12 * Kf s ^ 12 := by ring
  have hsumC : ∑ s ∈ F, Kf s ^ 12 ≤ 19500 * (n : ℝ) := by
    have := k_mean (n : ℝ) (Nat.cast_nonneg n)
    rw [Nat.floor_natCast] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hs.1.2⟩, ?_⟩
      by_contra h
      have := s6_r_odd s h
      omega
    · intros; positivity
  have hFR : F.card ≤ R.card := by
    apply Finset.card_le_card
    intro s hs
    simp only [hF, hR, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hs ⊢
    exact ⟨by omega, hs.2⟩
  have hFR' : (F.card : ℝ) ≤ R.card := by exact_mod_cast hFR
  have hq : ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 12 ≤ (105737 / 10000) ^ 12 * (19500 * (n : ℝ)) := by
    calc _ ≤ ∑ s ∈ F, (105737 / 10000) ^ 12 * Kf s ^ 12 := Finset.sum_le_sum hterm
      _ = (105737 / 10000) ^ 12 * ∑ s ∈ F, Kf s ^ 12 := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  rw [← hWF] at hH
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hW4 : (8477 / 10000 * (n : ℝ)) ^ 12 ≤ (∑ s ∈ Ioc n0 n, (r s : ℝ) * (log s ^ 2 / s)) ^ 12 :=
    pow_le_pow_left₀ (by positivity) hW 12
  have hq0 : 0 ≤ ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 12 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (exp_pos _) hn
  have key : (8477 / 10000 * (n : ℝ)) ^ 12 ≤ (R.card : ℝ) ^ 11 * ((105737 / 10000) ^ 12 * (19500 * (n : ℝ))) := by
    calc _ ≤ _ := hW4
      _ ≤ _ := hH
      _ ≤ (R.card : ℝ) ^ 11 * ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 12 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hFR' 11) hq0
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  by_contra hcon
  push Not at hcon
  have hc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have h3 : (R.card : ℝ) ^ 11 ≤ ((n : ℝ) / 39) ^ 11 := pow_le_pow_left₀ hc0 hcon.le 11
  have h4 : (R.card : ℝ) ^ 11 * ((105737 / 10000) ^ 12 * (19500 * (n : ℝ)))
      ≤ ((n : ℝ) / 39) ^ 11 * ((105737 / 10000) ^ 12 * (19500 * (n : ℝ))) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : ((n : ℝ) / 39) ^ 11 * ((105737 / 10000) ^ 12 * (19500 * (n : ℝ))) < (8477 / 10000 * (n : ℝ)) ^ 12 := by
    have hn4 : 0 < (n : ℝ) ^ 12 := by positivity
    have e1 : ((n : ℝ) / 39) ^ 11 * ((105737 / 10000) ^ 12 * (19500 * (n : ℝ)))
        = (105737 / 10000) ^ 12 * 19500 / 39 ^ 11 * (n : ℝ) ^ 12 := by ring
    have e2 : (8477 / 10000 * (n : ℝ)) ^ 12 = (8477 / 10000) ^ 12 * (n : ℝ) ^ 12 := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_right (by norm_num) hn4
  linarith

end P41

-- ===== Final =====
/-! Density `σ(A) ≥ 1/20`, Mann's theorem, and the `41` goal. -/

open Finset Real

namespace P41
open Schnir

-- ===== part d =====

theorem s6d_zero_mem_B : 0 ∈ B := ⟨3, Nat.prime_three, by norm_num, rfl⟩

theorem s6d_B_sub_A : B ⊆ A := by
  intro b hb
  open Pointwise in exact Set.mem_add.2 ⟨0, s6d_zero_mem_B, b, hb, zero_add b⟩

theorem s6d_one_mem_A : 1 ∈ A :=
  s6d_B_sub_A ⟨5, by norm_num, by norm_num, rfl⟩

theorem s6d_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

open Classical in
/-- Medium range: `#(A ∩ [1,N]) + 2 ≥ π(2N+3)`. -/
theorem s6d_medium (N : ℕ) :
    Nat.primeCounting (2 * N + 3) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
  set T := (range (2 * N + 4)).filter (fun p => p.Prime ∧ 5 ≤ p) with hT
  have h1 : Nat.primeCounting (2 * N + 3) ≤ #T + 2 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (2 * N + 3 + 1)).filter Nat.Prime ⊆ insert 2 (insert 3 T) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_insert, hT, mem_filter, mem_range]
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨by omega, hp.2, h5⟩)
      · have := hp.2.two_le
        interval_cases p
        · simp
        · simp
        · exact absurd hp.2 (by norm_num)
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans ?_
    have := card_insert_le 3 T
    omega
  have h2 : #T ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
    have hinj : Set.InjOn (fun p => (p - 3) / 2) (T : Set ℕ) := by
      intro p hp q hq hpq
      simp only [hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hp hq
      have := s6d_odd_of_prime hp.2.1 (by omega)
      have := s6d_odd_of_prime hq.2.1 (by omega)
      simp only at hpq
      omega
    rw [← card_image_of_injOn hinj]
    apply card_le_card
    intro a ha
    simp only [hT, mem_image, mem_filter, mem_range] at ha
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩ := ha
    have := s6d_odd_of_prime hp2 (by omega)
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, s6d_B_sub_A ⟨p, hp2, by omega, rfl⟩⟩
  omega

open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem s6d_large (N : ℕ) :
    #((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by
  set T := (range (2 * N + 6 + 1)).filter (fun s => 0 < r s) with hT
  have hmem : ∀ s ∈ T, ∃ p q, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ s = p + q ∧ s ≤ 2 * N + 6 := by
    intro s hs
    simp only [hT, mem_filter, mem_range] at hs
    obtain ⟨hs1, hs2⟩ := hs
    unfold r at hs2
    obtain ⟨p, hp⟩ := card_pos.1 hs2
    simp only [mem_filter, mem_range] at hp
    exact ⟨p, s - p, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by omega, by omega⟩
  have hinj : Set.InjOn (fun s => (s - 6) / 2) (T : Set ℕ) := by
    intro s hs t ht hst
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, -⟩ := hmem s hs
    obtain ⟨p', q', hp', hp2', hq', hq2', rfl, -⟩ := hmem t ht
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := s6d_odd_of_prime hp' hp2'
    have := s6d_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := hp.two_le; have := hq.two_le
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h0 : (p + q - 6) / 2 = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      have : (p + q - 6) / 2 = (p - 3) / 2 + (q - 3) / 2 := by omega
      rw [this]
      open Pointwise in
      exact Set.mem_add.2 ⟨(p - 3) / 2, ⟨p, hp, hp2, rfl⟩, (q - 3) / 2, ⟨q, hq, hq2, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem s6d_two_mem_A : 2 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 1, ⟨5, by norm_num, by norm_num, rfl⟩, rfl⟩

theorem s6d_three_mem_A : 3 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩


theorem n9_mem_B (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : (p - 3) / 2 ∈ B := ⟨p, hp, h2, rfl⟩

theorem n9_small_mem_A (a : ℕ) (h1 : 1 ≤ a) (h10 : a ≤ 10) : a ∈ A := by
  have b0 : 0 ∈ B := n9_mem_B 3 (by norm_num) (by norm_num)
  have b1 : 1 ∈ B := n9_mem_B 5 (by norm_num) (by norm_num)
  have b2 : 2 ∈ B := n9_mem_B 7 (by norm_num) (by norm_num)
  have b4 : 4 ∈ B := n9_mem_B 11 (by norm_num) (by norm_num)
  have b5 : 5 ∈ B := n9_mem_B 13 (by norm_num) (by norm_num)
  open Pointwise in
  interval_cases a
  · exact Set.mem_add.2 ⟨0, b0, 1, b1, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨2, b2, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨5, b5, 5, b5, rfl⟩

open Classical in
/-- `σ(A) ≥ 1/20`. -/
theorem density_A : (1 : ℝ) / 20 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 200
  · by_cases h10 : 10 ≤ N
    · have h1 : Icc 1 10 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, n9_small_mem_A a ha.1 ha.2⟩
      have h2 := card_le_card h1
      have h3' : (10 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 200 := by exact_mod_cast hsmall
      linarith
    · have h1 : Icc 1 N ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, ha.2⟩, n9_small_mem_A a ha.1 (by omega)⟩
      have h2 := card_le_card h1
      have h3' : (N : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast (show N ≤ _ by omega)
      linarith
  push Not at hsmall
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hsmall
  have hL := s6d_large N
  have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
      ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
  have hy6 : (0 : ℝ) < ((2 * N + 6 : ℕ) : ℝ) := by push_cast; linarith
  by_cases hbig : exp 2000 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := R_large _ hbig
    have hx := exp99_ge 2000 (by norm_num)
    push_cast at hR hbig
    linarith
  push Not at hbig
  by_cases hmid : 30 ≤ log ((2 * N + 6 : ℕ) : ℝ)
  · have hlog : log ((2 * N + 6 : ℕ) : ℝ) ≤ 2000 := by
      rw [log_le_iff_le_exp hy6]; exact hbig.le
    have hR := rv_range _ hmid hlog
    have hx : exp 30 ≤ ((2 * N + 6 : ℕ) : ℝ) := by
      rw [← exp_log hy6]; exact exp_le_exp.2 hmid
    have hx' : (10 : ℝ) ^ 12 ≤ exp 30 := (exp_ge_poly 30 (by norm_num)).trans' (by norm_num)
    push_cast at hR hx
    linarith
  · push Not at hmid
    have hy : (30 : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hP := Chebyshev.psi_lower _ hy
    have hpi := Chebyshev.psi_le_primeCounting_mul_log (2 * N + 3)
    have ha := Chebyshev.a_bound.1
    have hM := s6d_medium N
    have hM' : (Nat.primeCounting (2 * N + 3) : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
      exact_mod_cast hM
    have hypos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by linarith
    have hlogpos : 0 < log ((2 * N + 3 : ℕ) : ℝ) := log_pos (by linarith)
    have hlog36 : log ((2 * N + 3 : ℕ) : ℝ) ≤ log ((2 * N + 6 : ℕ) : ℝ) :=
      log_le_log hypos (by push_cast; linarith)
    have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting (2 * N + 3) : ℝ) := Nat.cast_nonneg _
    have hma : Chebyshev.a * ((2 * N + 3 : ℕ) : ℝ) ≥ 0.9212 * ((2 * N + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right ha hypos.le
    by_cases hlo : N < 100000
    · have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 13 := by
        rw [log_lt_iff_lt_exp hypos]
        have he := exp_one_gt_d9
        have h13 : exp 13 = exp 1 ^ 13 := by rw [← exp_nat_mul]; norm_num
        have h3 : (2.7182818283 : ℝ) ^ 13 ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) he.le 13
        have hN5 : (N : ℝ) < 100000 := by exact_mod_cast hlo
        push_cast
        nlinarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 13 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 13 := by linarith
      push_cast at hma hP hpi hmul hlog5 hlog
      nlinarith
    · push Not at hlo
      have hN5 : (100000 : ℝ) ≤ N := by exact_mod_cast hlo
      have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 30 := by linarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 30 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 30 := by linarith
      push_cast at hma hP hpi hmul hlog5 hlog
      nlinarith

open Pointwise

theorem s6m_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def s6m_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem s6m_P_add {j k t u : ℕ} (h1 : s6m_P j t) (h2 : s6m_P k u) : s6m_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem s6m_P_B {b : ℕ} (hb : b ∈ B) : s6m_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem s6m_P_A {a : ℕ} (ha : a ∈ A) : s6m_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact s6m_P_add (s6m_P_B hb) (s6m_P_B hc)


theorem n9_P_multiset (t : Multiset ℕ) (ht : ∀ x ∈ t, x ∈ A) : s6m_P (2 * t.card) t.sum := by
  induction t using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | cons a t ih =>
    have h1 := ih (fun x hx => ht x (Multiset.mem_cons_of_mem hx))
    have h2 := s6m_P_A (ht a (Multiset.mem_cons_self a t))
    have := s6m_P_add h2 h1
    rw [Multiset.card_cons, Multiset.sum_cons]
    rwa [show 2 * (t.card + 1) = 2 + 2 * t.card by ring]

open Classical in
theorem n9_all (t : ℕ) : s6m_P 40 t := by
  have hA := density_A
  have hk : (1 : ℝ) ≤ ((20 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 20 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd `n ≥ 83` is a sum of exactly `41` primes. -/
theorem exact_41 (n : ℕ) (hodd : Odd n) (hn : 83 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 41 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 123 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all ((n - 123) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 82) 3 + Multiset.replicate (123 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end P41

/-- The campaign goal (platform theorem `odd_sum_le_41_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 41 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 83 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := P41.exact_41 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega
