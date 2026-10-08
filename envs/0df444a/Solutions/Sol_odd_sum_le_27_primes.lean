-- Prove2me | solution 1 for odd_sum_le_27_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T18:30:32.960354+00:00
-- url     : https://prove2.me/submissions/fe1655c0-3df0-4ef3-8e56-89782f953b2e

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_basis_of_density
import Theorems.Thm_RV27_middle_range
import Theorems.Thm_RV27_large_range

/-!
Every odd `n > 1` is a sum of at most `27` primes.

`A = B + B` with `B = {(p - 3)/2 : p odd prime}`; we show `σ(A) ≥ 1/13` and apply Mann's theorem
(platform `Schnir.basis_of_density`), giving `26` odd primes plus one `3`.
* `N ≤ 130`: `A ⊇ [1, 10]`;
* `log(2N+6) < 23`: Chebyshev's `ψ(x) ≥ a x - 5 log x + 5` (`a ≈ 0.9212`) via `ψ(x) ≤ π(x) log x`;
* `23 ≤ log(2N+6) ≤ 300`: platform `RV27.middle_range` (Riesel–Vaughan small shifts with Siebert's bound);
* `log(2N+6) ≥ 300`: platform `RV27.large_range` (Riesel–Vaughan large range).
In the last two cases `#{s ≤ 2N+6 : r(s) > 0} ≥ (2N+6)/25`, and `(2N+6)/25 - 1 ≥ N/13` for `N ≥ 247`.
-/

-- ===== Chebyshev =====
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

namespace P27
open Schnir Finset Real


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
/-- `σ(A) ≥ 1/13`. -/
theorem density_A : (1 : ℝ) / 13 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 130
  · by_cases h10 : 10 ≤ N
    · have h1 : Icc 1 10 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, n9_small_mem_A a ha.1 ha.2⟩
      have h2 := card_le_card h1
      have h3' : (10 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 130 := by exact_mod_cast hsmall
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
  have hN' : (131 : ℝ) ≤ N := by exact_mod_cast hsmall
  have hL := s6d_large N
  have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
      ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
  have hy6 : (0 : ℝ) < ((2 * N + 6 : ℕ) : ℝ) := by push_cast; linarith
  have hx23 : (10 : ℝ) ^ 9 ≤ exp 23 := by
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have e : exp 23 = exp 1 ^ 23 := by rw [← exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 9 ≤ 2.7 ^ 23 := by norm_num
      _ ≤ exp 1 ^ 23 := pow_le_pow_left₀ (by norm_num) h3 23
  by_cases hbig : exp 300 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := RV27.large_range _ hbig
    have hx : exp 23 ≤ exp 300 := exp_le_exp.2 (by norm_num)
    push_cast at hR hbig
    linarith
  push Not at hbig
  by_cases hmid : 23 ≤ log ((2 * N + 6 : ℕ) : ℝ)
  · have hlog : log ((2 * N + 6 : ℕ) : ℝ) ≤ 300 := by
      rw [log_le_iff_le_exp hy6]; exact hbig.le
    have hR := RV27.middle_range _ hmid hlog
    have hx : exp 23 ≤ ((2 * N + 6 : ℕ) : ℝ) := by
      rw [← exp_log hy6]; exact exp_le_exp.2 hmid
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
      have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 23 := by linarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 23 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 23 := by linarith
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
theorem n9_all (t : ℕ) : s6m_P 26 t := by
  have hA := density_A
  have hk : (1 : ℝ) ≤ ((13 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 13 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd `n ≥ 55` is a sum of exactly `27` primes. -/
theorem exact_27 (n : ℕ) (hodd : Odd n) (hn : 55 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 27 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 81 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all ((n - 81) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 54) 3 + Multiset.replicate (81 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end P27

/-- The campaign goal (platform theorem `odd_sum_le_27_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 27 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 55 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := P27.exact_27 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega
