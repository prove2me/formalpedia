-- Prove2me | solution 1 for odd_sum_le_85_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-05T06:17:45.939866+00:00
-- url     : https://prove2.me/submissions/36ba5483-7a4a-4a31-a3eb-e646eab9ba0d

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_G_lower
import Theorems.Thm_Schnir_sieve_ineq
import Theorems.Thm_Schnir_basis_of_density

/-!
Every odd `n > 1` is a sum of at most `85` primes.

`A = B + B` with `B = {(p - 3)/2 : p odd prime}`; we show `σ(A) ≥ 1/42` and apply Mann's theorem
(platform `Schnir.basis_of_density`), giving `84` odd primes plus one `3`.
* `n ≤ 420`: `A ⊇ [1, 10]`;
* `log(2N+3) < 76`: Chebyshev's `ψ(x) ≥ a x - 5 log x + 5` (`a ≈ 0.9212`, `Chebyshev.psi_lower`, ported
  from PrimeNumberTheoremAnd) via `ψ(x) ≤ π(x) log x`;
* `76 ≤ log n ≤ 7000`: Riesel–Vaughan small shifts. With `Q` the first `300` odd primes,
  `R(s) = #{a ∈ Q : s - a odd prime}`; Cauchy–Schwarz gives `#{s ≤ n : R(s) > 0} ≥ (∑R)²/∑R²`.
  `∑R` uses `psi_lower`; the off-diagonal of `∑R²` counts prime pairs `(m, m + d)`, bounded by a
  Selberg sieve for `a(a+d)` (adapted from `Schnir.sieve_ineq`) and `Schnir.G_lower`, with
  `∑_{b<a ∈ Q} C(a-b) ≤ 215845` checked by the kernel;
* `log n ≥ 7000`: the Hölder argument of the `241` entry with `a ≈ 0.9212` in place of `2/3`.
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

-- ===== Sieve =====
/-!
Prime-pair Selberg sieve for a fixed even shift `d`, adapted from the proved `Schnir.sieve_ineq`
(polynomial `a (a + d)` on `[1, Y]` in place of `a (s - a)` on `[1, s]`).
-/

open Finset Real

namespace P85
open Schnir

theorem sieve_rho_le_two (s p : ℕ) : rho s p ≤ 2 := by unfold rho; split_ifs <;> omega
theorem sieve_one_le_rho (s p : ℕ) : 1 ≤ rho s p := by unfold rho; split_ifs <;> omega

theorem sieve_rho_lt (s p : ℕ) (hs : 2 ∣ s) (hp : p.Prime) : rho s p < p := by
  unfold rho
  rcases eq_or_ne p 2 with rfl | h2
  · simp [hs]
  · have := hp.two_le
    split_ifs <;> omega

/-- the sieve density `ν(m) = ρ(m)/m` -/
noncomputable def sieve_nu (s : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (rho s p : ℝ) / p)

theorem sieve_nu_prime (s p : ℕ) (hp : p.Prime) : sieve_nu s p = (rho s p : ℝ) / p := by
  simp [sieve_nu, hp.ne_zero, hp.primeFactors]

/-- `PS d Y z`: number of `1 ≤ a ≤ Y` such that `a (a + d)` has no prime divisor `≤ z`. -/
noncomputable def PS (d Y : ℕ) (z : ℝ) : ℕ :=
  ((Finset.Icc 1 Y).filter
    (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (a + d))).card

noncomputable def pair_BS (d : ℕ) (hd : 2 ∣ d) (Y N : ℕ) : BoundingSieve where
  support := (Icc 1 Y).image (fun a => a * (a + d))
  prodPrimes := primorial N
  prodPrimes_squarefree := squarefree_primorial N
  weights n := (#{a ∈ Icc 1 Y | a * (a + d) = n} : ℝ)
  weights_nonneg n := by positivity
  totalMass := Y
  nu := sieve_nu d
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp _ := by
    rw [sieve_nu_prime d p hp]
    have := sieve_one_le_rho d p
    have := hp.pos
    positivity
  nu_lt_one_of_prime p hp _ := by
    rw [sieve_nu_prime d p hp, div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast sieve_rho_lt d p hd hp

/-- number of roots of `x (x + d) = 0` in `ZMod m` -/
noncomputable def pair_R (d m : ℕ) : ℕ := Nat.card {x : ZMod m // x * (x + (d : ZMod m)) = 0}

theorem pair_R_mul (d m n : ℕ) (h : m.Coprime n) :
    pair_R d (m * n) = pair_R d m * pair_R d n := by
  unfold pair_R
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  refine (Equiv.subtypeEquiv e.toEquiv ?_).trans (Equiv.subtypeProdEquivProd)
  intro x
  have : e (x * (x + (d : ZMod (m * n)))) = (e x) * (e x + (d : ZMod m × ZMod n)) := by
    simp [map_mul, map_add, map_natCast]
  rw [← map_eq_zero_iff e e.injective, this]
  simp [Prod.ext_iff]

theorem pair_R_prime (d p : ℕ) (hp : p.Prime) : pair_R d p = rho d p := by
  have := Fact.mk hp
  unfold pair_R
  have : {x : ZMod p // x * (x + (d : ZMod p)) = 0} =
      {x : ZMod p // x ∈ ({0, -(d : ZMod p)} : Finset (ZMod p))} := by
    congr 1; ext x
    simp [mul_eq_zero, add_eq_zero_iff_eq_neg]
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold rho
  by_cases hs : p ∣ d
  · have : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hs
    simp [this, hs]
  · have : (d : ZMod p) ≠ 0 := fun h => hs ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have : (0 : ZMod p) ≠ -(d : ZMod p) := by
      intro h; apply this; rw [eq_comm, neg_eq_zero] at h; exact h
    rw [Finset.card_pair this]
    simp [hs]

theorem pair_R_one (d : ℕ) : pair_R d 1 = 1 := by
  unfold pair_R
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

theorem pair_R_prod (d : ℕ) (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    pair_R d (∏ p ∈ t, p) = ∏ p ∈ t, rho d p := by
  induction t using Finset.induction_on with
  | empty => simp [pair_R_one]
  | insert a t ha ih =>
    rw [prod_insert ha, prod_insert ha, pair_R_mul, pair_R_prime d a (ht a (by simp)),
      ih (fun p hp => ht p (by simp [hp]))]
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes (ht a (by simp)) (ht q (by simp [hq]))).2 (by rintro rfl; exact ha hq)

theorem pair_R_squarefree (d m : ℕ) (hm : Squarefree m) :
    pair_R d m = ∏ p ∈ m.primeFactors, rho d p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hm]
  exact pair_R_prod d _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
theorem sieve_count_residue (s d v : ℕ) (hd : 0 < d) :
    |(#{a ∈ Icc 1 s | a ≡ v [MOD d]} : ℝ) - s / d| ≤ 1 := by
  have key := Nat.Ioc_filter_modEq_card 0 s hd v
  have hI : Ioc 0 s = Icc 1 s := by ext a; simp; omega
  rw [hI] at key
  set c : ℕ := #{a ∈ Icc 1 s | a ≡ v [MOD d]}
  set x : ℚ := ((s : ℚ) - v) / d
  set y : ℚ := (((0:ℕ) : ℚ) - v) / d
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hxy : x - y = s / d := by simp only [x, y]; field_simp; ring
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hnn : 0 ≤ ⌊x⌋ - ⌊y⌋ := by
    have : ((-1 : ℤ) : ℚ) < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) := by
      push_cast
      have : (0 : ℚ) ≤ s / d := by positivity
      linarith
    have := Int.cast_lt.1 this
    omega
  rw [max_eq_left hnn] at key
  have hq : |(c : ℚ) - s / d| ≤ 1 := by
    have : (c : ℚ) = ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) := by exact_mod_cast key
    rw [this, abs_le]; push_cast
    constructor <;> linarith
  have : |(c : ℝ) - s / d| = ((|(c : ℚ) - s / d| : ℚ) : ℝ) := by push_cast; rfl
  rw [this]
  exact_mod_cast hq

theorem pair_multSum (d : ℕ) (hd : 2 ∣ d) (Y N m : ℕ) :
    (pair_BS d hd Y N).multSum m = #{a ∈ Icc 1 Y | m ∣ a * (a + d)} := by
  simp only [BoundingSieve.multSum, pair_BS]
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 Y) (t := (Icc 1 Y).image (fun a => a * (a + d)))
    (g := fun a => a * (a + d)) (fun a ha => mem_image_of_mem _ ha)]
  apply sum_congr rfl
  intro n _
  split_ifs with h
  · rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_filter]
    apply sum_congr rfl
    intro a _
    split_ifs with h1 h2 <;> simp_all
  · symm
    apply sum_eq_zero
    intro a ha
    rw [(mem_filter.1 ha).2]
    simp [h]

theorem pair_count_dvd (d Y m : ℕ) (hm : m ≠ 0) :
    |(#{a ∈ Icc 1 Y | m ∣ a * (a + d)} : ℝ) - Y * (pair_R d m) / m| ≤ pair_R d m := by
  have : NeZero m := ⟨hm⟩
  set t : Finset (ZMod m) := univ.filter (fun x => x * (x + (d : ZMod m)) = 0) with ht
  have hR : pair_R d m = #t := by
    unfold pair_R
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmem : ∀ a ∈ Icc 1 Y, m ∣ a * (a + d) ↔ (a : ZMod m) ∈ t := by
    intro a _
    rw [ht, mem_filter, ← ZMod.natCast_eq_zero_iff]
    push_cast
    simp
  have h1 : #{a ∈ Icc 1 Y | m ∣ a * (a + d)} = ∑ r ∈ t, #{a ∈ Icc 1 Y | a ≡ r.val [MOD m]} := by
    rw [card_eq_sum_card_fiberwise (f := fun a : ℕ => (a : ZMod m)) (t := t) ?_]
    · apply sum_congr rfl
      intro r hr
      congr 1
      ext a
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨ha, -⟩, rfl⟩
        exact ⟨ha, by rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]⟩
      · rintro ⟨ha, hm⟩
        have : (a : ZMod m) = r := by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hm; exact hm
        exact ⟨⟨ha, (hmem a ha).2 (this ▸ hr)⟩, this⟩
    · intro a ha
      rw [coe_filter] at ha
      exact (hmem a ha.1).1 ha.2
  rw [h1, hR, Nat.cast_sum]
  have : (Y : ℝ) * (#t : ℕ) / m = ∑ r ∈ t, (Y : ℝ) / m := by
    rw [sum_const, nsmul_eq_mul]; ring
  rw [this, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ((#t : ℕ) : ℝ) = ∑ r ∈ t, (1 : ℝ) := by simp
  rw [this]
  exact sum_le_sum (fun r _ => sieve_count_residue Y m r.val (Nat.pos_of_ne_zero hm))

theorem pair_rem_le (d : ℕ) (hd : 2 ∣ d) (Y N m : ℕ) (hm : m ∣ primorial N) :
    |(pair_BS d hd Y N).rem m| ≤ ∏ p ∈ m.primeFactors, (rho d p : ℝ) := by
  have hsq : Squarefree m := (squarefree_primorial N).squarefree_of_dvd hm
  have hm0 : m ≠ 0 := hsq.ne_zero
  have hnu : (pair_BS d hd Y N).nu m = (pair_R d m : ℝ) / m := by
    simp only [pair_BS, sieve_nu, ArithmeticFunction.prodPrimeFactors_apply hm0]
    rw [pair_R_squarefree d m hsq, prod_div_distrib]
    push_cast
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  simp only [BoundingSieve.rem]
  rw [pair_multSum, hnu]
  have := pair_count_dvd d Y m hm0
  rw [pair_R_squarefree d m hsq] at this ⊢
  push_cast at this ⊢
  simp only [pair_BS]
  convert this using 2
  ring

theorem pair_BS_prodPrimes (d : ℕ) (hd : 2 ∣ d) (Y N : ℕ) :
    (pair_BS d hd Y N).prodPrimes = primorial N := rfl
theorem pair_BS_support (d : ℕ) (hd : 2 ∣ d) (Y N : ℕ) :
    (pair_BS d hd Y N).support = (Icc 1 Y).image (fun a => a * (a + d)) := rfl
theorem pair_BS_weights (d : ℕ) (hd : 2 ∣ d) (Y N n : ℕ) :
    (pair_BS d hd Y N).weights n = (#{a ∈ Icc 1 Y | a * (a + d) = n} : ℝ) := rfl
theorem pair_BS_nu (d : ℕ) (hd : 2 ∣ d) (Y N : ℕ) :
    (pair_BS d hd Y N).nu = sieve_nu d := rfl
theorem pair_BS_totalMass (d : ℕ) (hd : 2 ∣ d) (Y N : ℕ) :
    (pair_BS d hd Y N).totalMass = Y := rfl

theorem pair_siftedSum (d : ℕ) (hd : 2 ∣ d) (Y : ℕ) (z : ℝ) :
    (pair_BS d hd Y ⌊z⌋₊).siftedSum = PS d Y z := by
  rw [BoundingSieve.siftedSum, pair_BS_prodPrimes, pair_BS_support]
  simp only [pair_BS_weights, PS]
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 Y) (t := (Icc 1 Y).image (fun a => a * (a + d)))
    (g := fun a => a * (a + d)) (fun a ha => mem_image_of_mem _ ha)]
  apply sum_congr rfl
  intro n _
  have hiff : Nat.Coprime (primorial ⌊z⌋₊) n ↔
      ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ n := by
    rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd]
    push Not
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      exact ⟨p, mem_range.2 (Nat.lt_succ_of_le ((hp.dvd_primorial_iff).1 h1)), hp, h2⟩
    · rintro ⟨p, h1, hp, h2⟩
      exact ⟨p, hp, (hp.dvd_primorial_iff).2 (Nat.le_of_lt_succ (mem_range.1 h1)), h2⟩
  by_cases hC : Nat.Coprime (primorial ⌊z⌋₊) n
  · rw [if_pos hC, card_eq_sum_ones, Nat.cast_sum]
    apply sum_congr rfl
    intro a ha
    rw [if_pos (by rw [(mem_filter.1 ha).2]; exact hiff.1 hC)]
  · rw [if_neg hC]; symm; apply sum_eq_zero; intro a ha
    rw [if_neg (by rw [(mem_filter.1 ha).2]; exact fun h => hC (hiff.2 h))]

theorem sieve_sum_moebius_filter (m l : ℕ) (hm : Squarefree m) :
    ∑ d ∈ m.divisors with l ∣ d, (ArithmeticFunction.moebius d : ℝ) =
      if l = m then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  have hm0 : m ≠ 0 := hm.ne_zero
  by_cases hlm : l ∣ m
  · obtain ⟨k, rfl⟩ := hlm
    have hl0 : l ≠ 0 := left_ne_zero_of_mul hm0
    have hk0 : k ≠ 0 := right_ne_zero_of_mul hm0
    have hcop : Nat.Coprime l k := Nat.coprime_of_squarefree_mul hm
    have himg : {d ∈ (l * k).divisors | l ∣ d} = k.divisors.image (fun e => l * e) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨⟨hd, -⟩, e, rfl⟩
        exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hl0) hd, hk0⟩, rfl⟩
      · rintro ⟨e, ⟨he, -⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left l he, hm0⟩, dvd_mul_right _ _⟩
    rw [himg, sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) hab)]
    have : ∀ e ∈ k.divisors, (ArithmeticFunction.moebius (l * e) : ℝ) =
        ArithmeticFunction.moebius l * ArithmeticFunction.moebius e := by
      intro e he
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors he))]
      push_cast; ring
    rw [sum_congr rfl this, ← mul_sum]
    have hz : ∑ e ∈ k.divisors, (ArithmeticFunction.moebius e : ℝ) = if k = 1 then 1 else 0 := by
      have := congrArg (fun f : ArithmeticFunction ℝ => f k)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
      simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
      rw [← this]
      simp
    rw [hz]
    by_cases hk : k = 1
    · simp [hk]
    · have : l ≠ l * k := by
        intro h; apply hk
        exact (Nat.mul_eq_left hl0).1 h.symm
      simp [hk, this]
  · have hne : l ≠ m := by rintro rfl; exact hlm dvd_rfl
    rw [if_neg hne]
    apply sum_eq_zero
    intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) hlm
    

open scoped ArithmeticFunction.Moebius in
/-- Selberg's weights at level `N`. -/
noncomputable def sieve_w (B : BoundingSieve) (N : ℕ) (d : ℕ) : ℝ :=
  if d ≤ N then
    (μ d : ℝ) / (B.nu d * ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) *
      ∑ m ∈ B.prodPrimes.divisors with d ∣ m ∧ m ≤ N, B.selbergTerms m
  else 0

open scoped ArithmeticFunction.Moebius in
theorem sieve_nu_mul_w (B : BoundingSieve) (N d : ℕ) (hd : d ∈ B.prodPrimes.divisors) :
    B.nu d * sieve_w B N d = (μ d : ℝ) / (∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) *
      ∑ m ∈ B.prodPrimes.divisors with d ∣ m ∧ m ≤ N, B.selbergTerms m := by
  have hnu : B.nu d ≠ 0 := BoundingSieve.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
  unfold sieve_w
  split_ifs with h
  · rw [← mul_assoc, mul_div_assoc', mul_div_mul_left _ _ hnu]
  · rw [mul_zero, eq_comm]
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro m hm
    rw [mem_filter] at hm
    obtain ⟨hm, hdm, hmN⟩ := hm
    exfalso
    have : m ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hm)
    exact h ((Nat.le_of_dvd (Nat.pos_of_ne_zero this) hdm).trans hmN)


open scoped ArithmeticFunction.Moebius in
theorem sieve_inner (B : BoundingSieve) (N l : ℕ) (hl : l ∈ B.prodPrimes.divisors) :
    ∑ d ∈ B.prodPrimes.divisors, (if l ∣ d then B.nu d * sieve_w B N d else 0) =
      if l ≤ N then (μ l : ℝ) * B.selbergTerms l /
        (∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l) else 0 := by
  set D := B.prodPrimes.divisors with hD
  set Gd := ∑ l ∈ D with l ≤ N, B.selbergTerms l with hGd
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  calc ∑ d ∈ D, (if l ∣ d then B.nu d * sieve_w B N d else 0)
      = ∑ d ∈ D, ∑ m ∈ D,
          (if l ∣ d ∧ d ∣ m ∧ m ≤ N then (μ d : ℝ) / Gd * B.selbergTerms m else 0) := by
        apply sum_congr rfl; intro d hd
        by_cases hld : l ∣ d
        · rw [if_pos hld, sieve_nu_mul_w B N d hd, mul_sum, sum_filter]
          apply sum_congr rfl; intro m _
          by_cases h2 : d ∣ m ∧ m ≤ N
          · rw [if_pos h2, if_pos ⟨hld, h2⟩]
          · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        · rw [if_neg hld]; symm; apply sum_eq_zero; intro m _
          rw [if_neg (fun h => hld h.1)]
    _ = ∑ m ∈ D, ∑ d ∈ D,
          (if l ∣ d ∧ d ∣ m ∧ m ≤ N then (μ d : ℝ) / Gd * B.selbergTerms m else 0) := sum_comm
    _ = ∑ m ∈ D, (if m ≤ N then B.selbergTerms m / Gd *
          ∑ d ∈ m.divisors with l ∣ d, (μ d : ℝ) else 0) := by
        apply sum_congr rfl; intro m hm
        by_cases hmN : m ≤ N
        · rw [if_pos hmN, mul_sum, ← Nat.divisors_filter_dvd_of_dvd hP (Nat.dvd_of_mem_divisors hm),
            filter_filter, sum_filter]
          apply sum_congr rfl; intro d _
          by_cases h : l ∣ d ∧ d ∣ m
          · rw [if_pos ⟨h.1, h.2, hmN⟩, if_pos ⟨h.2, h.1⟩]; ring
          · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
        · rw [if_neg hmN]; apply sum_eq_zero; intro d _
          rw [if_neg (fun h => hmN h.2.2)]
    _ = ∑ m ∈ D, (if l = m then (if l ≤ N then (μ l : ℝ) * B.selbergTerms l / Gd else 0)
          else 0) := by
        apply sum_congr rfl; intro m hm
        rw [sieve_sum_moebius_filter m l
          (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hm)]
        by_cases hlm : l = m
        · subst hlm; simp only [if_true]
          split_ifs <;> ring
        · simp [hlm]
    _ = _ := by rw [sum_ite_eq D l]; rw [if_pos hl]


theorem sieve_Gd_pos (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) :
    0 < ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l := by
  apply sum_pos'
  · intro l hl
    exact (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.1 hl).1)).le
  · refine ⟨1, mem_filter.2 ⟨Nat.one_mem_divisors.2 BoundingSieve.prodPrimes_ne_zero, hN⟩, ?_⟩
    exact BoundingSieve.selbergTerms_pos (one_dvd _)

theorem sieve_w_one (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) : sieve_w B N 1 = 1 := by
  have := sieve_Gd_pos B N hN
  unfold sieve_w
  rw [if_pos hN]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, B.nu_mult.map_one, one_mul,
    one_dvd, true_and]
  field_simp

theorem sieve_mainSum (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) :
    B.mainSum (BoundingSieve.lambdaSquared (sieve_w B N)) =
      1 / ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l := by
  have hG := sieve_Gd_pos B N hN
  set Gd := ∑ l ∈ B.prodPrimes.divisors with l ≤ N, B.selbergTerms l with hGd
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  rw [sum_congr rfl (fun l hl => by rw [sieve_inner B N l hl])]
  have : ∀ l ∈ B.prodPrimes.divisors, (B.selbergTerms l)⁻¹ *
      (if l ≤ N then (ArithmeticFunction.moebius l : ℝ) * B.selbergTerms l / Gd else 0) ^ 2 =
      if l ≤ N then B.selbergTerms l / Gd ^ 2 else 0 := by
    intro l hl
    have hpos := BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    have hmu : ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hl)
    split_ifs
    · field_simp
      exact hmu
    · simp
  rw [sum_congr rfl this, ← sum_filter, ← sum_div, ← hGd]
  field_simp


theorem sieve_w_abs_le (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) (d : ℕ)
    (hd : d ∈ B.prodPrimes.divisors) : |sieve_w B N d| ≤ 1 := by
  have hG := sieve_Gd_pos B N hN
  set D := B.prodPrimes.divisors with hD
  set Gd := ∑ l ∈ D with l ≤ N, B.selbergTerms l with hGd
  have hdP : d ∣ B.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hnu : 0 < B.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
  have hmult := BoundingSieve.selbergTerms_isMultiplicative (s := B)
  unfold sieve_w
  split_ifs with hdN
  swap
  · simp
  set M := {m ∈ D | d ∣ m ∧ m ≤ N} with hM
  set Bd := {b ∈ D | b ∣ d} with hBd
  have hMmem : ∀ m ∈ M, m ∈ D ∧ d ∣ m ∧ m ≤ N := fun m hm => by
    simpa [hM] using hm
  have hBmem : ∀ b ∈ Bd, b ∈ D ∧ b ∣ d := fun b hb => by
    simpa [hBd] using hb
  -- decomposition m = d * k with k coprime to d
  have hdec : ∀ m ∈ M, d * (m / d) = m ∧ Nat.Coprime d (m / d) := by
    intro m hm
    obtain ⟨hmD, hdm, -⟩ := hMmem m hm
    have e : d * (m / d) = m := Nat.mul_div_cancel' hdm
    refine ⟨e, Nat.coprime_of_squarefree_mul ?_⟩
    rw [e]; exact BoundingSieve.squarefree_of_mem_divisors_prodPrimes hmD
  have key : ∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹ ≤ Gd := by
    calc ∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹
        = ∑ m ∈ M, ∑ b ∈ Bd, B.selbergTerms (b * (m / d)) := by
          apply sum_congr rfl; intro m hm
          obtain ⟨e, hcop⟩ := hdec m hm
          conv_lhs => rw [← e]
          rw [hmult.map_mul_of_coprime hcop, mul_right_comm,
            ← BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP,
            ← sum_filter, sum_mul]
          apply sum_congr rfl; intro b hb
          rw [hmult.map_mul_of_coprime (hcop.coprime_dvd_left (hBmem b hb).2)]
      _ = ∑ x ∈ M ×ˢ Bd, B.selbergTerms (x.2 * (x.1 / d)) := by rw [sum_product]
      _ = ∑ l ∈ (M ×ˢ Bd).image (fun x => x.2 * (x.1 / d)), B.selbergTerms l := by
          rw [sum_image]
          rintro ⟨m1, b1⟩ h1 ⟨m2, b2⟩ h2 heq
          simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
          simp only at heq
          obtain ⟨e1, c1⟩ := hdec m1 h1.1
          obtain ⟨e2, c2⟩ := hdec m2 h2.1
          have hb1 := (hBmem b1 h1.2).2
          have hb2 := (hBmem b2 h2.2).2
          have g1 : Nat.gcd (b1 * (m1 / d)) d = b1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel _ c1.symm, Nat.gcd_eq_left hb1]
          have g2 : Nat.gcd (b2 * (m2 / d)) d = b2 := by
            rw [Nat.Coprime.gcd_mul_right_cancel _ c2.symm, Nat.gcd_eq_left hb2]
          have hbb : b1 = b2 := by rw [← g1, ← g2, heq]
          subst hbb
          have hb0 : 0 < b1 := Nat.pos_of_dvd_of_pos hb1 hd0
          have hk : m1 / d = m2 / d := Nat.eq_of_mul_eq_mul_left hb0 heq
          have : m1 = m2 := by rw [← e1, ← e2, hk]
          rw [this]
      _ ≤ Gd := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro l hl
            rw [mem_image] at hl
            obtain ⟨⟨m, b⟩, hx, rfl⟩ := hl
            rw [mem_product] at hx
            obtain ⟨hmD, hdm, hmN⟩ := hMmem m hx.1
            obtain ⟨e, -⟩ := hdec m hx.1
            have hb := (hBmem b hx.2).2
            have hdiv : b * (m / d) ∣ m := by
              conv_rhs => rw [← e]
              exact Nat.mul_dvd_mul_right hb _
            have hm0 : 0 < m := Nat.pos_of_mem_divisors hmD
            rw [mem_filter]
            refine ⟨Nat.mem_divisors.2 ⟨hdiv.trans (Nat.dvd_of_mem_divisors hmD), hP⟩, ?_⟩
            exact (Nat.le_of_dvd hm0 hdiv).trans hmN
          · intro l hl _
            exact (BoundingSieve.selbergTerms_pos
              (Nat.dvd_of_mem_divisors (mem_filter.1 hl).1)).le
  have hSnn : 0 ≤ ∑ m ∈ M, B.selbergTerms m := sum_nonneg (fun m hm =>
    (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (hMmem m hm).1)).le)
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_mul, abs_div, abs_of_pos (mul_pos hnu hG), abs_of_nonneg hSnn]
  calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (B.nu d * Gd) * ∑ m ∈ M, B.selbergTerms m
      ≤ 1 / (B.nu d * Gd) * ∑ m ∈ M, B.selbergTerms m :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmu (mul_pos hnu hG).le) hSnn
    _ = (∑ m ∈ M, B.selbergTerms m * (B.nu d)⁻¹) / Gd := by
        rw [← sum_mul]; field_simp
    _ ≤ Gd / Gd := div_le_div_of_nonneg_right key hG.le
    _ = 1 := div_self hG.ne'


theorem sieve_errSum_le (B : BoundingSieve) (N : ℕ) (hN : 1 ≤ N) (R : ℕ → ℝ)
    (hR0 : ∀ d ∈ B.prodPrimes.divisors, 0 ≤ R d)
    (hrem : ∀ d ∈ B.prodPrimes.divisors, |B.rem d| ≤ R d)
    (hRl : ∀ a ∈ B.prodPrimes.divisors, ∀ b ∈ B.prodPrimes.divisors,
      R (Nat.lcm a b) ≤ R a * R b) :
    B.errSum (BoundingSieve.lambdaSquared (sieve_w B N)) ≤
      (∑ d ∈ B.prodPrimes.divisors with d ≤ N, R d) ^ 2 := by
  set D := B.prodPrimes.divisors with hD
  set w := sieve_w B N with hw
  have hP : B.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hsub : ∀ d ∈ D, d.divisors ⊆ D := fun d hd =>
    Nat.divisors_subset_of_dvd hP (Nat.dvd_of_mem_divisors hd)
  have hlcm : ∀ a ∈ D, ∀ b ∈ D, Nat.lcm a b ∈ D := fun a ha b hb =>
    Nat.mem_divisors.2 ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb), hP⟩
  have hwabs : ∀ d ∈ D, |w d| ≤ 1 := fun d hd => sieve_w_abs_le B N hN d hd
  have hwN : ∀ d, ¬ d ≤ N → w d = 0 := fun d hd => by simp [hw, sieve_w, hd]
  unfold BoundingSieve.errSum
  calc ∑ d ∈ D, |BoundingSieve.lambdaSquared w d| * |B.rem d|
      ≤ ∑ d ∈ D, (∑ d1 ∈ D, ∑ d2 ∈ D,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) * R d := by
        apply sum_le_sum; intro d hd
        apply mul_le_mul _ (hrem d hd) (abs_nonneg _) (sum_nonneg fun _ _ =>
          sum_nonneg fun _ _ => by positivity)
        unfold BoundingSieve.lambdaSquared
        refine (abs_sum_le_sum_abs _ _).trans ?_
        refine (sum_le_sum fun d1 _ => abs_sum_le_sum_abs _ _).trans ?_
        have e : ∀ d1 d2, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| =
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
          intro d1 d2; split_ifs <;> simp [abs_mul]
        simp only [e]
        refine (sum_le_sum fun d1 _ => sum_le_sum_of_subset_of_nonneg (hsub d hd)
          (fun _ _ _ => by positivity)).trans ?_
        apply sum_le_sum_of_subset_of_nonneg (hsub d hd)
        intro _ _ _; exact sum_nonneg fun _ _ => by positivity
    _ = ∑ d1 ∈ D, ∑ d2 ∈ D, |w d1| * |w d2| * R (Nat.lcm d1 d2) := by
        simp_rw [sum_mul, ite_mul, zero_mul]
        rw [sum_comm]
        apply sum_congr rfl; intro d1 hd1
        rw [sum_comm]
        apply sum_congr rfl; intro d2 hd2
        rw [sum_ite_eq', if_pos (hlcm d1 hd1 d2 hd2)]
    _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, (if d1 ≤ N then R d1 else 0) * (if d2 ≤ N then R d2 else 0) := by
        apply sum_le_sum; intro d1 hd1
        apply sum_le_sum; intro d2 hd2
        by_cases h1 : d1 ≤ N
        · by_cases h2 : d2 ≤ N
          · rw [if_pos h1, if_pos h2]
            calc |w d1| * |w d2| * R (Nat.lcm d1 d2) ≤ 1 * 1 * R (Nat.lcm d1 d2) := by
                  apply mul_le_mul_of_nonneg_right _ (hR0 _ (hlcm d1 hd1 d2 hd2))
                  exact mul_le_mul (hwabs d1 hd1) (hwabs d2 hd2) (abs_nonneg _) zero_le_one
              _ ≤ R d1 * R d2 := by rw [one_mul, one_mul]; exact hRl d1 hd1 d2 hd2
          · rw [hwN d2 h2]; simp [h2]
        · rw [hwN d1 h1]; simp [h1]
    _ = (∑ d ∈ D with d ≤ N, R d) ^ 2 := by
        rw [sq, sum_filter, sum_mul_sum]


theorem pair_selbergTerms_eq (d : ℕ) (hd : 2 ∣ d) (Y N m : ℕ) (hm : m ≠ 0) :
    (pair_BS d hd Y N).selbergTerms m = hfun d m := by
  rw [BoundingSieve.selbergTerms_apply, pair_BS_nu, sieve_nu,
    ArithmeticFunction.prodPrimeFactors_apply hm, ← prod_mul_distrib, hfun]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [← sieve_nu, sieve_nu_prime d p hpp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hlt : (rho d p : ℝ) < p := by exact_mod_cast sieve_rho_lt d p hd hpp
  have hpr : (p : ℝ) - rho d p ≠ 0 := by linarith
  rw [one_sub_div hp0, inv_div]
  field_simp

theorem pair_G_eq (d : ℕ) (hd : 2 ∣ d) (Y : ℕ) (z : ℝ) :
    G d z = ∑ l ∈ (pair_BS d hd Y ⌊z⌋₊).prodPrimes.divisors with l ≤ ⌊z⌋₊,
      (pair_BS d hd Y ⌊z⌋₊).selbergTerms l := by
  unfold G
  have hset : (Icc 1 ⌊z⌋₊).filter Squarefree =
      (pair_BS d hd Y ⌊z⌋₊).prodPrimes.divisors.filter (· ≤ ⌊z⌋₊) := by
    rw [pair_BS_prodPrimes]
    ext l
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hsq⟩
      exact ⟨⟨hsq.dvd_primorial.trans (primorial_dvd_primorial h2), primorial_ne_zero _⟩, h2⟩
    · rintro ⟨⟨hdvd, -⟩, h2⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hdvd (primorial_pos _), h2⟩, ?_⟩
      exact (squarefree_primorial _).squarefree_of_dvd hdvd
  rw [hset]
  apply sum_congr rfl
  intro l hl
  rw [pair_selbergTerms_eq d hd Y _ l (Nat.pos_of_mem_divisors (mem_filter.1 hl).1).ne']

theorem sieve_prod_rho_le_card_divisors (s d : ℕ) (hd : d ≠ 0) :
    ∏ p ∈ d.primeFactors, rho s p ≤ #d.divisors := by
  rw [Nat.card_divisors hd]
  apply prod_le_prod'
  intro p hp
  have : 1 ≤ d.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hd (Nat.dvd_of_mem_primeFactors hp)
  have := sieve_rho_le_two s p
  omega

open Pointwise in
theorem sieve_card_divisors_lcm_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    #(Nat.lcm a b).divisors ≤ #a.divisors * #b.divisors := by
  calc #(Nat.lcm a b).divisors ≤ #(a * b).divisors :=
        card_le_card (Nat.divisors_subset_of_dvd (mul_ne_zero ha hb) (Nat.lcm_dvd_mul a b))
    _ = #(a.divisors * b.divisors) := by rw [Nat.divisors_mul]
    _ ≤ _ := card_mul_le

theorem sieve_sum_card_divisors (N : ℕ) :
    ∑ d ∈ Icc 1 N, (#d.divisors : ℝ) ≤ N * (1 + Real.log N) := by
  have h1 : ∀ d ∈ Icc 1 N, (#d.divisors : ℝ) = ∑ k ∈ Icc 1 N, if k ∣ d then (1 : ℝ) else 0 := by
    intro d hd
    rw [mem_Icc] at hd
    rw [← sum_filter, sum_const, nsmul_one]
    congr 2
    ext k
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hk, -⟩
      have := Nat.le_of_dvd (by omega) hk
      have := Nat.pos_of_dvd_of_pos hk (by omega)
      exact ⟨⟨by omega, by omega⟩, hk⟩
    · rintro ⟨-, hk⟩; exact ⟨hk, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ k ∈ Icc 1 N, (∑ d ∈ Icc 1 N, if k ∣ d then (1 : ℝ) else 0) = ((N / k : ℕ) : ℝ) := by
    intro k _
    rw [← sum_filter, sum_const, nsmul_one, ← Nat.Ioc_filter_dvd_card_eq_div N k]
    congr 3
  rw [sum_congr rfl h2]
  calc ∑ k ∈ Icc 1 N, ((N / k : ℕ) : ℝ) ≤ ∑ k ∈ Icc 1 N, (N : ℝ) * (k : ℝ)⁻¹ := by
        apply sum_le_sum; intro k _
        rw [← div_eq_mul_inv]; exact Nat.cast_div_le
    _ = N * (harmonic N : ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ N * (1 + Real.log N) := by
        gcongr; exact harmonic_le_one_add_log N


/-- Prime-pair Selberg sieve: `PS d Y z ≤ Y / G_d(z) + z^2 (1 + log z)^2` for even `d > 0`. -/
theorem pair_sieve (d : ℕ) (hd : Even d) (Y : ℕ) (z : ℝ) (hz : 1 < z) :
    (PS d Y z : ℝ) ≤ Y / G d z + z ^ 2 * (1 + Real.log z) ^ 2 := by
  have hs2 : 2 ∣ d := even_iff_two_dvd.1 hd
  have hN : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hmain := (pair_BS d hs2 Y ⌊z⌋₊).siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared _ (sieve_w_one (pair_BS d hs2 Y ⌊z⌋₊) ⌊z⌋₊ hN))
  rw [pair_siftedSum, pair_BS_totalMass, sieve_mainSum _ _ hN, ← pair_G_eq] at hmain
  have herr := sieve_errSum_le (pair_BS d hs2 Y ⌊z⌋₊) ⌊z⌋₊ hN (fun m => (#m.divisors : ℝ))
    (fun m _ => by positivity)
    (fun m hm => by
      have hmP := Nat.dvd_of_mem_divisors hm
      have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
      refine (pair_rem_le d hs2 Y ⌊z⌋₊ m hmP).trans ?_
      exact_mod_cast sieve_prod_rho_le_card_divisors d m hm0)
    (fun a ha b hb => by
      exact_mod_cast sieve_card_divisors_lcm_le a b (Nat.pos_of_mem_divisors ha).ne'
        (Nat.pos_of_mem_divisors hb).ne')
  have hsum : ∑ m ∈ (pair_BS d hs2 Y ⌊z⌋₊).prodPrimes.divisors with m ≤ ⌊z⌋₊, (#m.divisors : ℝ)
      ≤ z * (1 + Real.log z) := by
    calc _ ≤ ∑ m ∈ Icc 1 ⌊z⌋₊, (#m.divisors : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [mem_filter] at hm
            exact mem_Icc.2 ⟨Nat.pos_of_mem_divisors hm.1, hm.2⟩
          · intro _ _ _; positivity
      _ ≤ ⌊z⌋₊ * (1 + Real.log ⌊z⌋₊) := sieve_sum_card_divisors _
      _ ≤ z * (1 + Real.log z) := by
          have h1 : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hN
          have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
          have h3 : Real.log ⌊z⌋₊ ≤ Real.log z := Real.log_le_log (by linarith) h2
          have h4 : 0 ≤ Real.log ⌊z⌋₊ := Real.log_nonneg h1
          apply mul_le_mul h2 (by linarith) (by linarith) (by linarith)
  have hsum0 : 0 ≤ ∑ m ∈ (pair_BS d hs2 Y ⌊z⌋₊).prodPrimes.divisors with m ≤ ⌊z⌋₊,
      (#m.divisors : ℝ) := sum_nonneg fun _ _ => by positivity
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc (PS d Y z : ℝ) ≤ Y * (1 / G d z) + _ := hmain
    _ ≤ Y * (1 / G d z) + (z * (1 + Real.log z)) ^ 2 := by
        gcongr; exact herr.trans hsq
    _ = Y / G d z + z ^ 2 * (1 + Real.log z) ^ 2 := by ring

end P85

-- ===== Pair =====
open Finset Real

namespace P85
open Schnir

/-! ## Prime pairs with a fixed shift -/

/-- number of `m ≤ Y` with `m` and `m + d` both prime. -/
noncomputable def PPc (d Y : ℕ) : ℕ := #{m ∈ range (Y + 1) | m.Prime ∧ (m + d).Prime}

theorem PPc_le_PS (d Y : ℕ) (z : ℝ) (hz : 1 < z) :
    (PPc d Y : ℝ) ≤ z + PS d Y z := by
  have hsub : {m ∈ range (Y + 1) | m.Prime ∧ (m + d).Prime} ⊆
      Icc 1 ⌊z⌋₊ ∪ (Icc 1 Y).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (a + d)) := by
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨hmY, hmp, hmdp⟩ := hm
    have hm1 := hmp.one_lt
    by_cases h1 : m ≤ ⌊z⌋₊
    · exact mem_union_left _ (mem_Icc.2 ⟨by omega, h1⟩)
    · apply mem_union_right
      simp only [mem_filter, mem_Icc, Finset.mem_range]
      refine ⟨⟨by omega, by omega⟩, fun p hp hpp hdvd => ?_⟩
      rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpp hmp).1 h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hpp hmdp).1 h; omega
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.card_Icc] at hc
  have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have : (PPc d Y : ℝ) ≤ (⌊z⌋₊ + 1 - 1 : ℕ) + PS d Y z := by
    unfold PPc PS; exact_mod_cast hc
  simp only [Nat.add_sub_cancel] at this
  linarith

/-- Prime pairs with shift `d`: `#{m ≤ Y : m, m + d prime} ≤ z + 2 C(d) Y / log² z + z² (1 + log z)²`. -/
theorem PPc_le (d Y : ℕ) (hd : Even d) (hd0 : 0 < d) (z : ℝ) (hz : 1 < z) :
    (PPc d Y : ℝ) ≤ z + 2 * C d * Y / (Real.log z) ^ 2 + z ^ 2 * (1 + Real.log z) ^ 2 := by
  have h1 := PPc_le_PS d Y z hz
  have h2 := pair_sieve d hd Y z hz
  have hG := G_lower d hd hd0 z hz
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hC : 0 < C d := by
    unfold C
    apply prod_pos
    intro p _
    have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  have hGpos : 0 < G d z := lt_of_lt_of_le (by positivity) hG
  have h3 : (Y : ℝ) / G d z ≤ 2 * C d * Y / (Real.log z) ^ 2 := by
    rw [div_le_div_iff₀ hGpos (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hG
    have hY : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
    nlinarith
  linarith

/-! ## A computable upper bound for `C d`, `d < 2256` -/

def Sset : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

/-- `1 + p/(p-1)^2` -/
noncomputable def fC (p : ℕ) : ℝ := 1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2

def Wt (d : ℕ) : ℕ := ∏ p ∈ Sset, (if p ∣ d then (p - 1) ^ 2 + p else (p - 1) ^ 2)

def Dd : ℕ := ∏ p ∈ Sset, (p - 1) ^ 2

theorem Sset_prime : ∀ p ∈ Sset, p.Prime ∧ 3 ≤ p := by
  intro p hp
  simp only [Sset, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem fC_two : fC 2 = 3 := by norm_num [fC]

theorem one_le_fC (p : ℕ) : 1 ≤ fC p := by
  unfold fC
  have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
  linarith

theorem fC_le_47 (p : ℕ) (hp : 47 ≤ p) : fC p ≤ fC 47 := by
  unfold fC
  have h : (47 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  push_cast
  rw [add_le_add_iff_left, div_le_div_iff₀ h1 (by norm_num)]
  nlinarith

theorem fC_term (p d : ℕ) (hp : 3 ≤ p) :
    (if p ∣ d then fC p else 1) =
      (((if p ∣ d then (p - 1) ^ 2 + p else (p - 1) ^ 2 : ℕ) : ℝ) / (((p - 1) ^ 2 : ℕ) : ℝ)) := by
  have hc : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hne : ((p : ℝ) - 1) ^ 2 ≠ 0 := hpos.ne'
  split_ifs
  · unfold fC
    push_cast [hc]
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  · push_cast [hc]
    rw [div_self hne]

theorem prod_S_eq (d : ℕ) :
    ∏ p ∈ Sset, (if p ∣ d then fC p else 1) = (Wt d : ℝ) / Dd := by
  rw [prod_congr rfl (fun p hp => fC_term p d (Sset_prime p hp).2), prod_div_distrib]
  unfold Wt Dd
  rw [Nat.cast_prod, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
theorem C_le_Wt (d : ℕ) (hd : Even d) (hd0 : 0 < d) (hdl : d < 2256) :
    C d ≤ 3 * fC 47 * (Wt d : ℝ) / Dd := by
  have hd2 : 2 ∣ d := even_iff_two_dvd.1 hd
  have hCf : C d = ∏ p ∈ d.primeFactors, fC p := rfl
  rw [hCf, ← prod_filter_mul_prod_filter_not d.primeFactors (fun p => p < 47)]
  -- small primes
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
  rw [hsmall, prod_filter, prod_insert h2S, if_pos hd2, fC_two, prod_S_eq]
  -- large primes
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
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : 47 * 48 ≤ a * b := Nat.mul_le_mul ha47 (by omega)
      omega
    · have : 48 * 47 ≤ a * b := Nat.mul_le_mul (by omega) hb47
      omega
  have hB : ∏ p ∈ Bf, fC p ≤ fC 47 := by
    calc ∏ p ∈ Bf, fC p ≤ ∏ p ∈ Bf, fC 47 := by
          apply prod_le_prod (fun p _ => by linarith [one_le_fC p])
          intro p hp
          simp only [hBf, mem_filter] at hp
          exact fC_le_47 p (by omega)
      _ = fC 47 ^ Bf.card := by rw [prod_const]
      _ ≤ fC 47 ^ 1 := pow_le_pow_right₀ (one_le_fC 47) hcard
      _ = fC 47 := pow_one _
  have hW : (0 : ℝ) ≤ (Wt d : ℝ) / Dd := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc 3 * ((Wt d : ℝ) / Dd) * ∏ p ∈ Bf, fC p ≤ 3 * ((Wt d : ℝ) / Dd) * fC 47 :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num) hW)
    _ = 3 * fC 47 * (Wt d : ℝ) / Dd := by ring

end P85

-- ===== TSum =====
/-! The small primes `Q` (the first 300 odd primes) and the weight sum `T`. -/

open Finset Real

namespace P85
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
def Qc15 : List ℕ := [881, 883, 887, 907, 911, 919, 929, 937, 941, 947]
def Qc16 : List ℕ := [953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
def Qc17 : List ℕ := [1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087]
def Qc18 : List ℕ := [1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153]
def Qc19 : List ℕ := [1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229]
def Qc20 : List ℕ := [1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297]
def Qc21 : List ℕ := [1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]
def Qc22 : List ℕ := [1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453]
def Qc23 : List ℕ := [1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523]
def Qc24 : List ℕ := [1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597]
def Qc25 : List ℕ := [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663]
def Qc26 : List ℕ := [1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741]
def Qc27 : List ℕ := [1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823]
def Qc28 : List ℕ := [1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901]
def Qc29 : List ℕ := [1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993]
def Qlist : List ℕ := Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 ++ Qc15 ++ Qc16 ++ Qc17 ++ Qc18 ++ Qc19 ++ Qc20 ++ Qc21 ++ Qc22 ++ Qc23 ++ Qc24 ++ Qc25 ++ Qc26 ++ Qc27 ++ Qc28 ++ Qc29
theorem Qlist_nodup : Qlist.Nodup := by decide +kernel

def Qs : Finset ℕ := ⟨(Qlist : Multiset ℕ), Multiset.coe_nodup.2 Qlist_nodup⟩

theorem Qc0_prime : ∀ p ∈ Qc0, p.Prime := by
  simp only [Qc0, List.forall_mem_cons]
  norm_num

theorem Qc1_prime : ∀ p ∈ Qc1, p.Prime := by
  simp only [Qc1, List.forall_mem_cons]
  norm_num

theorem Qc2_prime : ∀ p ∈ Qc2, p.Prime := by
  simp only [Qc2, List.forall_mem_cons]
  norm_num

theorem Qc3_prime : ∀ p ∈ Qc3, p.Prime := by
  simp only [Qc3, List.forall_mem_cons]
  norm_num

theorem Qc4_prime : ∀ p ∈ Qc4, p.Prime := by
  simp only [Qc4, List.forall_mem_cons]
  norm_num

theorem Qc5_prime : ∀ p ∈ Qc5, p.Prime := by
  simp only [Qc5, List.forall_mem_cons]
  norm_num

theorem Qc6_prime : ∀ p ∈ Qc6, p.Prime := by
  simp only [Qc6, List.forall_mem_cons]
  norm_num

theorem Qc7_prime : ∀ p ∈ Qc7, p.Prime := by
  simp only [Qc7, List.forall_mem_cons]
  norm_num

theorem Qc8_prime : ∀ p ∈ Qc8, p.Prime := by
  simp only [Qc8, List.forall_mem_cons]
  norm_num

theorem Qc9_prime : ∀ p ∈ Qc9, p.Prime := by
  simp only [Qc9, List.forall_mem_cons]
  norm_num

theorem Qc10_prime : ∀ p ∈ Qc10, p.Prime := by
  simp only [Qc10, List.forall_mem_cons]
  norm_num

theorem Qc11_prime : ∀ p ∈ Qc11, p.Prime := by
  simp only [Qc11, List.forall_mem_cons]
  norm_num

theorem Qc12_prime : ∀ p ∈ Qc12, p.Prime := by
  simp only [Qc12, List.forall_mem_cons]
  norm_num

theorem Qc13_prime : ∀ p ∈ Qc13, p.Prime := by
  simp only [Qc13, List.forall_mem_cons]
  norm_num

theorem Qc14_prime : ∀ p ∈ Qc14, p.Prime := by
  simp only [Qc14, List.forall_mem_cons]
  norm_num

theorem Qc15_prime : ∀ p ∈ Qc15, p.Prime := by
  simp only [Qc15, List.forall_mem_cons]
  norm_num

theorem Qc16_prime : ∀ p ∈ Qc16, p.Prime := by
  simp only [Qc16, List.forall_mem_cons]
  norm_num

theorem Qc17_prime : ∀ p ∈ Qc17, p.Prime := by
  simp only [Qc17, List.forall_mem_cons]
  norm_num

theorem Qc18_prime : ∀ p ∈ Qc18, p.Prime := by
  simp only [Qc18, List.forall_mem_cons]
  norm_num

theorem Qc19_prime : ∀ p ∈ Qc19, p.Prime := by
  simp only [Qc19, List.forall_mem_cons]
  norm_num

theorem Qc20_prime : ∀ p ∈ Qc20, p.Prime := by
  simp only [Qc20, List.forall_mem_cons]
  norm_num

theorem Qc21_prime : ∀ p ∈ Qc21, p.Prime := by
  simp only [Qc21, List.forall_mem_cons]
  norm_num

theorem Qc22_prime : ∀ p ∈ Qc22, p.Prime := by
  simp only [Qc22, List.forall_mem_cons]
  norm_num

theorem Qc23_prime : ∀ p ∈ Qc23, p.Prime := by
  simp only [Qc23, List.forall_mem_cons]
  norm_num

theorem Qc24_prime : ∀ p ∈ Qc24, p.Prime := by
  simp only [Qc24, List.forall_mem_cons]
  norm_num

theorem Qc25_prime : ∀ p ∈ Qc25, p.Prime := by
  simp only [Qc25, List.forall_mem_cons]
  norm_num

theorem Qc26_prime : ∀ p ∈ Qc26, p.Prime := by
  simp only [Qc26, List.forall_mem_cons]
  norm_num

theorem Qc27_prime : ∀ p ∈ Qc27, p.Prime := by
  simp only [Qc27, List.forall_mem_cons]
  norm_num

theorem Qc28_prime : ∀ p ∈ Qc28, p.Prime := by
  simp only [Qc28, List.forall_mem_cons]
  norm_num

theorem Qc29_prime : ∀ p ∈ Qc29, p.Prime := by
  simp only [Qc29, List.forall_mem_cons]
  norm_num

theorem Qlist_prime : ∀ p ∈ Qlist, p.Prime :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨Qc0_prime, Qc1_prime⟩, Qc2_prime⟩, Qc3_prime⟩, Qc4_prime⟩, Qc5_prime⟩, Qc6_prime⟩, Qc7_prime⟩, Qc8_prime⟩, Qc9_prime⟩, Qc10_prime⟩, Qc11_prime⟩, Qc12_prime⟩, Qc13_prime⟩, Qc14_prime⟩, Qc15_prime⟩, Qc16_prime⟩, Qc17_prime⟩, Qc18_prime⟩, Qc19_prime⟩, Qc20_prime⟩, Qc21_prime⟩, Qc22_prime⟩, Qc23_prime⟩, Qc24_prime⟩, Qc25_prime⟩, Qc26_prime⟩, Qc27_prime⟩, Qc28_prime⟩, Qc29_prime⟩

theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 1993 := by
  have hp' : p ∈ Qlist := Multiset.mem_coe.1 (Finset.mem_def.1 hp)
  refine ⟨Qlist_prime p hp', ?_, ?_⟩
  · have : ∀ q ∈ Qlist, q ≠ 2 := by decide +kernel
    exact this p hp'
  · have : ∀ q ∈ Qlist, q ≤ 1993 := by decide +kernel
    exact this p hp'

theorem Qs_card : Qs.card = 300 := by decide +kernel

/-- `Wt` written out, for fast kernel evaluation. -/
def Wt2 (d : ℕ) : ℕ := (if d % 3 = 0 then 7 else 4) * (if d % 5 = 0 then 21 else 16) * (if d % 7 = 0 then 43 else 36) * (if d % 11 = 0 then 111 else 100) * (if d % 13 = 0 then 157 else 144) * (if d % 17 = 0 then 273 else 256) * (if d % 19 = 0 then 343 else 324) * (if d % 23 = 0 then 507 else 484) * (if d % 29 = 0 then 813 else 784) * (if d % 31 = 0 then 931 else 900) * (if d % 37 = 0 then 1333 else 1296) * (if d % 41 = 0 then 1641 else 1600) * (if d % 43 = 0 then 1807 else 1764)

theorem Wt_eq (d : ℕ) : Wt d = Wt2 d := by
  simp only [Wt, Sset, Wt2]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_singleton]
  simp only [Nat.dvd_iff_mod_eq_zero]
  norm_num only [mul_assoc]

/-- one row of the weight sum -/
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then Wt2 (a - b) else 0).sum
theorem chunk0 : (Qc0.map rowW).sum ≤ 206062199273765158434310717440000 := by decide +kernel
theorem chunk1 : (Qc1.map rowW).sum ≤ 736528323627177815855427747840000 := by decide +kernel
theorem chunk2 : (Qc2.map rowW).sum ≤ 1274173712332287706466919383040000 := by decide +kernel
theorem chunk3 : (Qc3.map rowW).sum ≤ 1820847279807139022796824248320000 := by decide +kernel
theorem chunk4 : (Qc4.map rowW).sum ≤ 2348849043061154179394473820160000 := by decide +kernel
theorem chunk5 : (Qc5.map rowW).sum ≤ 2911705675856043133597699276800000 := by decide +kernel
theorem chunk6 : (Qc6.map rowW).sum ≤ 3452218137117113294073291079680000 := by decide +kernel
theorem chunk7 : (Qc7.map rowW).sum ≤ 3978471808348433652462177484800000 := by decide +kernel
theorem chunk8 : (Qc8.map rowW).sum ≤ 4525558747436020691072440074240000 := by decide +kernel
theorem chunk9 : (Qc9.map rowW).sum ≤ 5076132063464525806409676226560000 := by decide +kernel
theorem chunk10 : (Qc10.map rowW).sum ≤ 5633320486192733353127863910400000 := by decide +kernel
theorem chunk11 : (Qc11.map rowW).sum ≤ 6156612931747217771558244188160000 := by decide +kernel
theorem chunk12 : (Qc12.map rowW).sum ≤ 6689372579525061117709080802099200 := by decide +kernel
theorem chunk13 : (Qc13.map rowW).sum ≤ 7250387646744225301929707490508800 := by decide +kernel
theorem chunk14 : (Qc14.map rowW).sum ≤ 7791536693858630215888544779468800 := by decide +kernel
theorem chunk15 : (Qc15.map rowW).sum ≤ 8350317302760581090894306869248000 := by decide +kernel
theorem chunk16 : (Qc16.map rowW).sum ≤ 8901104243704354308154948426137600 := by decide +kernel
theorem chunk17 : (Qc17.map rowW).sum ≤ 9378145729594046825324909848166400 := by decide +kernel
theorem chunk18 : (Qc18.map rowW).sum ≤ 9969405706498886089553501120102400 := by decide +kernel
theorem chunk19 : (Qc19.map rowW).sum ≤ 10540934473419945656242759375257600 := by decide +kernel
theorem chunk20 : (Qc20.map rowW).sum ≤ 11024687354505666399784022940057600 := by decide +kernel
theorem chunk21 : (Qc21.map rowW).sum ≤ 11619073773762493593259764980121600 := by decide +kernel
theorem chunk22 : (Qc22.map rowW).sum ≤ 12129256269155195589916823755161600 := by decide +kernel
theorem chunk23 : (Qc23.map rowW).sum ≤ 12698189498469673563336361377792000 := by decide +kernel
theorem chunk24 : (Qc24.map rowW).sum ≤ 13203905158939933113411406764441600 := by decide +kernel
theorem chunk25 : (Qc25.map rowW).sum ≤ 13777512237249313603846560074956800 := by decide +kernel
theorem chunk26 : (Qc26.map rowW).sum ≤ 14310594345838437650982022152192000 := by decide +kernel
theorem chunk27 : (Qc27.map rowW).sum ≤ 14833362102568572756961935124070400 := by decide +kernel
theorem chunk28 : (Qc28.map rowW).sum ≤ 15394001651206972920253979924889600 := by decide +kernel
theorem chunk29 : (Qc29.map rowW).sum ≤ 15973422664996650574638873575424000 := by decide +kernel

theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∑ a ∈ Qs, f a = (Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist : Multiset ℕ)) = _
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem Qlist_eq : Qlist = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 ++ Qc15 ++ Qc16 ++ Qc17 ++ Qc18 ++ Qc19 ++ Qc20 ++ Qc21 ++ Qc22 ++ Qc23 ++ Qc24 ++ Qc25 ++ Qc26 ++ Qc27 ++ Qc28 ++ Qc29 := rfl

theorem row_eq (a : ℕ) : (∑ b ∈ Qs, if b < a then Wt (a - b) else 0) = rowW a := by
  rw [sum_Qs]
  simp only [Wt_eq, rowW]

/-- the half weight sum -/
theorem half_le : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wt (a - b) else 0) ≤ 241955689841062251957338857537536000 := by
  have h1 : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wt (a - b) else 0) = (Qlist.map rowW).sum := by
    rw [sum_Qs]
    simp only [row_eq]
  rw [h1, Qlist_eq]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (chunk0) chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14) chunk15) chunk16) chunk17) chunk18) chunk19) chunk20) chunk21) chunk22) chunk23) chunk24) chunk25) chunk26) chunk27) chunk28) chunk29).trans_eq (by norm_num)

theorem Dd_eq : Dd = 3437616625820471975215104000000 := by
  simp [Dd, Sset]

theorem T_bound :
    ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then C (a - b) else 0) ≤ 215845 := by
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then C (a - b) else 0) ≤
      3 * fC 47 / Dd * ((if b < a then Wt (a - b) else 0 : ℕ) : ℝ) := by
    intro a ha b hb
    obtain ⟨hap, ha2, ha1993⟩ := Qs_prop a ha
    obtain ⟨hbp, hb2, hb1993⟩ := Qs_prop b hb
    split_ifs with hab
    · have hao := hap.odd_of_ne_two ha2
      have hbo := hbp.odd_of_ne_two hb2
      have hev : Even (a - b) := by
        obtain ⟨i, hi⟩ := hao; obtain ⟨j, hj⟩ := hbo
        exact ⟨i - j, by omega⟩
      have := C_le_Wt (a - b) hev (by omega) (by omega)
      exact this.trans_eq (by ring)
    · simp
  have hD : (0 : ℝ) < Dd := by
    rw [Dd_eq]; norm_num
  have hk : 0 ≤ 3 * fC 47 / Dd := div_nonneg (by linarith [one_le_fC 47]) hD.le
  set H := (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wt (a - b) else 0 : ℕ) with hH
  have hHle : (H : ℝ) ≤ 241955689841062251957338857537536000 := by exact_mod_cast half_le
  have hcast : ((H : ℕ) : ℝ) = ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then Wt (a - b) else 0 : ℕ) : ℝ) := by
    rw [hH, Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
  calc ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then C (a - b) else 0)
      ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, 3 * fC 47 / Dd * ((if b < a then Wt (a - b) else 0 : ℕ) : ℝ) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
    _ = 3 * fC 47 / Dd * (H : ℝ) := by
        rw [hcast, mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
    _ ≤ 3 * fC 47 / Dd * (241955689841062251957338857537536000 : ℝ) := mul_le_mul_of_nonneg_left hHle hk
    _ ≤ 215845 := by
        rw [Dd_eq]; norm_num [fC]

end P85

-- ===== RV =====
/-! Riesel–Vaughan small shifts: representations `s = a + q` with `a ∈ Q`, `q` an odd prime. -/

open Finset Real

namespace P85
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

/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - 1993`. -/
theorem sumR_lower (n : ℕ) (hn : 1995 ≤ n) :
    300 * (oddP (n - 1993)).card ≤ ∑ s ∈ range (n + 1), Rr s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Qs, (oddP (n - 1993)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, ha1993⟩ := Qs_prop a ha
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
  calc 300 * (oddP (n - 1993)).card = ∑ _a ∈ Qs, (oddP (n - 1993)).card := by
        rw [sum_const, Qs_card, smul_eq_mul]
    _ ≤ _ := sum_le_sum h

/-- a pair `b < a` of shifts hits a prime pair `(s - a, s - b)`. -/
theorem pair_le (a b n : ℕ) (hba : b < a) :
    ∑ s ∈ range (n + 1), ind a s * ind b s ≤ PPc (a - b) n := by
  simp_rw [ind_mul]
  rw [← card_filter, PPc]
  apply card_le_card_of_injOn (fun s => s - a)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    obtain ⟨hs, ⟨has, hpa, -⟩, ⟨hbs, hpb, -⟩⟩ := hs
    refine ⟨by omega, hpa, ?_⟩
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
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPc (a - b) n else 0 := by
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

theorem pairs_card : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then 1 else 0 : ℕ) = 44850 := by
  decide +kernel

end P85

-- ===== RVPiece =====
/-! The analytic inequalities for one piece `La ≤ log n ≤ Lb` of the middle range. -/

open Finset Real

namespace P85
open Schnir

theorem exp99_ge (x : ℝ) (hx : 70 ≤ x) : (10 : ℝ) ^ 12 ≤ exp x := by
  have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
  have h : exp 70 = exp 2 ^ 35 := by rw [← exp_nat_mul]; norm_num
  calc (10 : ℝ) ^ 12 ≤ 3 ^ 35 := by norm_num
    _ ≤ exp 2 ^ 35 := pow_le_pow_left₀ (by norm_num) h3 35
    _ = exp 70 := h.symm
    _ ≤ exp x := exp_le_exp.2 hx

theorem C_nonneg (d : ℕ) : 0 ≤ C d := by
  unfold C
  apply prod_nonneg
  intro p _
  have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

/-- first moment, from Chebyshev's `ψ(m) ≥ a m - 5 log m + 5` (`a ≥ 0.9212`). -/
theorem X_lower (n : ℕ) (Lb : ℝ) (hn : (10 : ℝ) ^ 12 ≤ n) (hLb : log n ≤ Lb) (hLb12 : Lb ≤ 12000) :
    300 * 0.9211 / Lb * n ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
  have hn1995 : 1995 ≤ n := by exact_mod_cast (show (1995 : ℝ) ≤ n by linarith)
  set m := n - 1993 with hm
  have hmR : (m : ℝ) = n - 1993 := by rw [hm, Nat.cast_sub (by omega)]; norm_num
  have hX := sumR_lower n hn1995
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
  have hXc : (300 : ℝ) * (oddP m).card ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
    exact_mod_cast hX
  rw [div_mul_eq_mul_div, div_le_iff₀ hLbpos]
  have := mul_le_mul_of_nonneg_right hXc hLbpos.le
  linarith

/-- the off-diagonal (prime pair) part of the second moment. -/
theorem off_le (n : ℕ) (La Lb lb : ℝ) (h99 : 76 ≤ La) (h1 : La ≤ log n) (h2 : log n ≤ Lb)
    (hlb : Lb ≤ exp lb) (hu : 0 < La / 2 - 2 * lb) :
    ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPc (a - b) n else 0 : ℕ) : ℝ) ≤
      n * (2 * 44850 * (1 + (1 + Lb / 2) ^ 2) / La ^ 4 + 4 * 215845 / (La / 2 - 2 * lb) ^ 2) := by
  set L := log (n : ℝ) with hLdef
  have hL : 76 ≤ L := h99.trans h1
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [hLdef, h] at hL; simp at hL; linarith
    · exact_mod_cast h
  have hnexp : exp L = n := exp_log hnpos
  set E := exp (L / 2) with hEdef
  have hE2 : E ^ 2 = n := by rw [hEdef, sq, ← exp_add, ← hnexp]; congr 1; ring
  have hE3 : (L / 2) ^ 4 / 24 ≤ E := by
    have := pow_div_factorial_le_exp (x := L / 2) (by linarith) 4
    norm_num [Nat.factorial] at this
    exact this
  have hLpos : 0 < L := by linarith
  set z := E / L ^ 2 with hzdef
  have hz2 : 2 ≤ z := by
    rw [hzdef, le_div_iff₀ (by positivity)]
    have hL2 : 768 ≤ L ^ 2 := by nlinarith
    have h4 : (L / 2) ^ 4 / 24 = L ^ 2 * L ^ 2 / 384 := by ring
    nlinarith [sq_nonneg L]
  have hzsq : z ^ 2 = n / L ^ 4 := by rw [hzdef, div_pow, hE2, ← pow_mul]
  have hlogz : log z = L / 2 - 2 * log L := by
    rw [hzdef, log_div (exp_pos _).ne' (by positivity), log_exp, log_pow]
    push_cast; ring
  have hLbpos : 0 < Lb := by linarith
  have hlogL : log L ≤ lb :=
    (log_le_log hLpos (hLdef ▸ h2)).trans ((log_le_iff_le_exp hLbpos).2 hlb)
  have hlogL0 : 0 ≤ log L := log_nonneg (by linarith)
  set lz := log z with hlzdef
  have hlz1 : La / 2 - 2 * lb ≤ lz := by rw [hlogz]; linarith
  have hlz2 : lz ≤ Lb / 2 := by rw [hlogz]; linarith
  have hlz0 : 0 < lz := lt_of_lt_of_le hu hlz1
  -- termwise sieve bound
  have hpair : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then (PPc (a - b) n : ℝ) else 0) ≤
      (if b < a then (1 : ℝ) else 0) * (z + z ^ 2 * (1 + lz) ^ 2) +
        2 * n / lz ^ 2 * (if b < a then C (a - b) else 0) := by
    intro a ha b hb
    split_ifs with h
    · obtain ⟨hap, ha2, -⟩ := Qs_prop a ha
      obtain ⟨hbp, hb2, -⟩ := Qs_prop b hb
      have hev : Even (a - b) := by
        obtain ⟨i, hi⟩ := hap.odd_of_ne_two ha2
        obtain ⟨j, hj⟩ := hbp.odd_of_ne_two hb2
        exact ⟨i - j, by omega⟩
      have := PPc_le (a - b) n hev (by omega) z (by linarith)
      have e : 2 * C (a - b) * n / lz ^ 2 = 2 * n / lz ^ 2 * C (a - b) := by ring
      rw [← hlzdef] at this
      linarith
    · simp
  have hsum : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then (PPc (a - b) n : ℝ) else 0) ≤
      (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then (1 : ℝ) else 0) * (z + z ^ 2 * (1 + lz) ^ 2) +
        2 * n / lz ^ 2 * (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then C (a - b) else 0) := by
    calc _ ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then (1 : ℝ) else 0) * (z + z ^ 2 * (1 + lz) ^ 2) +
        2 * n / lz ^ 2 * (if b < a then C (a - b) else 0)) :=
          sum_le_sum fun a ha => sum_le_sum fun b hb => hpair a ha b hb
      _ = _ := by simp only [sum_add_distrib, ← sum_mul, ← mul_sum]
  have hP : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then (1 : ℝ) else 0) = 44850 := by
    have := congrArg (Nat.cast (R := ℝ)) pairs_card
    push_cast at this
    exact this
  have hT := T_bound
  have hT0 : 0 ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then C (a - b) else 0) :=
    sum_nonneg fun a _ => sum_nonneg fun b _ => by split_ifs <;> simp [C_nonneg]
  have hcast : ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPc (a - b) n else 0 : ℕ) : ℝ) =
      2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then (PPc (a - b) n : ℝ) else 0 := by
    push_cast; rfl
  rw [hcast]
  -- the pieces
  set w := (n : ℝ) / La ^ 4 with hw
  have hL4 : La ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
  have hzw : z ^ 2 ≤ w := by
    rw [hzsq, hw]; exact div_le_div_of_nonneg_left hnpos.le (by positivity) hL4
  have hz_le : z ≤ w := by nlinarith
  have h1lz : (1 + lz) ^ 2 ≤ (1 + Lb / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hA : z ^ 2 * (1 + lz) ^ 2 ≤ w * (1 + Lb / 2) ^ 2 :=
    mul_le_mul hzw h1lz (by positivity) (by positivity)
  set T' := ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then C (a - b) else 0) with hT'
  have hu2 : (La / 2 - 2 * lb) ^ 2 ≤ lz ^ 2 := pow_le_pow_left₀ hu.le hlz1 2
  have hB : T' / lz ^ 2 ≤ 215845 / (La / 2 - 2 * lb) ^ 2 :=
    div_le_div₀ (by norm_num) hT (by positivity) hu2
  have hB' : 2 * n / lz ^ 2 * T' = 2 * n * (T' / lz ^ 2) := by ring
  have hB2 : 2 * (n : ℝ) * (T' / lz ^ 2) ≤ 2 * n * (215845 / (La / 2 - 2 * lb) ^ 2) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hgoal : (n : ℝ) * (2 * 44850 * (1 + (1 + Lb / 2) ^ 2) / La ^ 4 + 4 * 215845 / (La / 2 - 2 * lb) ^ 2)
      = 2 * (44850 * (w + w * (1 + Lb / 2) ^ 2) + 2 * n * (215845 / (La / 2 - 2 * lb) ^ 2)) := by
    rw [hw]; ring
  rw [hgoal]
  rw [hP] at hsum
  linarith

/-- one piece of the middle range: `#{s ≤ n : r(s) > 0} ≥ n / 83`. -/
theorem rv_piece (n : ℕ) (La Lb lb : ℝ) (h99 : 76 ≤ La) (hLb12 : Lb ≤ 12000)
    (h1 : La ≤ log n) (h2 : log n ≤ Lb) (hlb : Lb ≤ exp lb) (hu : 0 < La / 2 - 2 * lb)
    (hnum : 300 * 0.9211 / Lb + (2 * 44850 * (1 + (1 + Lb / 2) ^ 2) / La ^ 4 +
      4 * 215845 / (La / 2 - 2 * lb) ^ 2) ≤ 83 * (300 * 0.9211 / Lb) ^ 2) :
    (n : ℝ) / 83 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  have hn12 : (10 : ℝ) ^ 12 ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at h1; simp at h1; linarith
      · exact_mod_cast h
    rw [← exp_log hnpos]; exact exp99_ge _ (by linarith)
  set x := 300 * 0.9211 / Lb with hx
  set k := 2 * 44850 * (1 + (1 + Lb / 2) ^ 2) / La ^ 4 + 4 * 215845 / (La / 2 - 2 * lb) ^ 2 with hk
  have hX := X_lower n Lb hn12 h2 hLb12
  have hoff := off_le n La Lb lb h99 h1 h2 hlb hu
  have hcs := rv_cs n
  have h2m := sumR2_le n
  set X := ∑ s ∈ range (n + 1), Rr s with hXdef
  set off := 2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPc (a - b) n else 0 with hoffdef
  set cnt := #{s ∈ range (n + 1) | 0 < r s} with hcnt
  have hcsN : X ^ 2 ≤ cnt * (X + off) := hcs.trans (Nat.mul_le_mul_left _ h2m)
  have hcsR : (X : ℝ) ^ 2 ≤ cnt * (X + off) := by exact_mod_cast hcsN
  have hLbpos : 0 < Lb := by linarith
  have hX' : (n : ℝ) * x ≤ X := by rw [hx, mul_comm]; exact hX
  have hoff' : (off : ℝ) ≤ n * k := by rw [hk]; exact hoff
  have hx298 : 1 / 166 ≤ x := by
    rw [hx, le_div_iff₀ hLbpos]; linarith
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
  have h4 : (cnt : ℝ) * (X + n * k) < n / 83 * (X + n * k) :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have p1 : 0 ≤ ((X : ℝ) - n * x) * (X + n * x - n / 83) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (n : ℝ) * (2 * x - 1 / 83) := mul_nonneg hn0 (by linarith)
    linarith
  have p2 : 0 ≤ (n : ℝ) ^ 2 * (83 * x ^ 2 - x - k) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (X : ℝ) ^ 2 - n / 83 * (X + n * k) =
      ((X : ℝ) - n * x) * (X + n * x - n / 83) + (n : ℝ) ^ 2 * (83 * x ^ 2 - x - k) / 83 := by
    ring
  linarith

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

end P85

-- ===== RVRange =====
/-! The middle range `76 ≤ log n ≤ 7000`, split into pieces. -/

open Finset Real

namespace P85
open Schnir

set_option maxHeartbeats 4000000 in
theorem rv_range (n : ℕ) (h1 : 76 ≤ log n) (h2 : log n ≤ 7000) :
    (n : ℝ) / 83 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  rcases le_or_gt (log (n : ℝ)) 78 with hb0 | ha0
  · exact rv_piece n 76 78 (2179 / 500 : ℝ) (by norm_num) (by norm_num) h1 hb0 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 81 with hb1 | ha1
  · exact rv_piece n 78 81 (1099 / 250 : ℝ) (by norm_num) (by norm_num) ha0.le hb1 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 85 with hb2 | ha2
  · exact rv_piece n 81 85 (1111 / 250 : ℝ) (by norm_num) (by norm_num) ha1.le hb2 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 90 with hb3 | ha3
  · exact rv_piece n 85 90 (4501 / 1000 : ℝ) (by norm_num) (by norm_num) ha2.le hb3 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 96 with hb4 | ha4
  · exact rv_piece n 90 96 (2283 / 500 : ℝ) (by norm_num) (by norm_num) ha3.le hb4 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 104 with hb5 | ha5
  · exact rv_piece n 96 104 (2323 / 500 : ℝ) (by norm_num) (by norm_num) ha4.le hb5 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 114 with hb6 | ha6
  · exact rv_piece n 104 114 (2369 / 500 : ℝ) (by norm_num) (by norm_num) ha5.le hb6 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 127 with hb7 | ha7
  · exact rv_piece n 114 127 (2423 / 500 : ℝ) (by norm_num) (by norm_num) ha6.le hb7 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 144 with hb8 | ha8
  · exact rv_piece n 127 144 (4971 / 1000 : ℝ) (by norm_num) (by norm_num) ha7.le hb8 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 166 with hb9 | ha9
  · exact rv_piece n 144 166 (5113 / 1000 : ℝ) (by norm_num) (by norm_num) ha8.le hb9 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 194 with hb10 | ha10
  · exact rv_piece n 166 194 (5269 / 1000 : ℝ) (by norm_num) (by norm_num) ha9.le hb10 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 231 with hb11 | ha11
  · exact rv_piece n 194 231 (1361 / 250 : ℝ) (by norm_num) (by norm_num) ha10.le hb11 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 279 with hb12 | ha12
  · exact rv_piece n 231 279 (5633 / 1000 : ℝ) (by norm_num) (by norm_num) ha11.le hb12 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 342 with hb13 | ha13
  · exact rv_piece n 279 342 (1459 / 250 : ℝ) (by norm_num) (by norm_num) ha12.le hb13 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 424 with hb14 | ha14
  · exact rv_piece n 342 424 (6051 / 1000 : ℝ) (by norm_num) (by norm_num) ha13.le hb14 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 531 with hb15 | ha15
  · exact rv_piece n 424 531 (1569 / 250 : ℝ) (by norm_num) (by norm_num) ha14.le hb15 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 670 with hb16 | ha16
  · exact rv_piece n 531 670 (6509 / 1000 : ℝ) (by norm_num) (by norm_num) ha15.le hb16 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 850 with hb17 | ha17
  · exact rv_piece n 670 850 (6747 / 1000 : ℝ) (by norm_num) (by norm_num) ha16.le hb17 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1081 with hb18 | ha18
  · exact rv_piece n 850 1081 (6987 / 1000 : ℝ) (by norm_num) (by norm_num) ha17.le hb18 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1375 with hb19 | ha19
  · exact rv_piece n 1081 1375 (1807 / 250 : ℝ) (by norm_num) (by norm_num) ha18.le hb19 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 1742 with hb20 | ha20
  · exact rv_piece n 1375 1742 (933 / 125 : ℝ) (by norm_num) (by norm_num) ha19.le hb20 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 2193 with hb21 | ha21
  · exact rv_piece n 1742 2193 (1539 / 200 : ℝ) (by norm_num) (by norm_num) ha20.le hb21 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 2734 with hb22 | ha22
  · exact rv_piece n 2193 2734 (1583 / 200 : ℝ) (by norm_num) (by norm_num) ha21.le hb22 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 3364 with hb23 | ha23
  · exact rv_piece n 2734 3364 (4061 / 500 : ℝ) (by norm_num) (by norm_num) ha22.le hb23 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 4072 with hb24 | ha24
  · exact rv_piece n 3364 4072 (8313 / 1000 : ℝ) (by norm_num) (by norm_num) ha23.le hb24 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 4837 with hb25 | ha25
  · exact rv_piece n 4072 4837 (4243 / 500 : ℝ) (by norm_num) (by norm_num) ha24.le hb25 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 5627 with hb26 | ha26
  · exact rv_piece n 4837 5627 (8637 / 1000 : ℝ) (by norm_num) (by norm_num) ha25.le hb26 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 6404 with hb27 | ha27
  · exact rv_piece n 5627 6404 (4383 / 500 : ℝ) (by norm_num) (by norm_num) ha26.le hb27 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)
  exact rv_piece n 6404 7000 (1771 / 200 : ℝ) (by norm_num) (by norm_num) ha27.le h2 ((exp_ge_poly _ (by norm_num)).trans' (by norm_num)) (by norm_num) (by norm_num)

end P85

-- ===== LargeBase =====
/-! Unchanged helper lemmas from the proved `241` entry (Schnirelmann large range). -/

open Finset Real

namespace P85
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

/-- Pairs counted by `r s` either have a small prime or are counted by `S s z`. -/
theorem n9_r_le_S (s : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (r s : ℝ) ≤ S s z + 2 * z := by
  have hsub : (Finset.range (s + 1)).filter
      (fun p => p.Prime ∧ p ≠ 2 ∧ (s - p).Prime ∧ s - p ≠ 2) ⊆
      (Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪
      (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hps, hpp, -, hqp, -⟩ := hp
    have hp1 := hpp.one_lt
    have hq1 := hqp.one_lt
    by_cases h1 : p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_Icc]; left; left; omega
    by_cases h2 : s - p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]; left; right
      exact ⟨s - p, ⟨by omega, h2⟩, by omega⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    right
    refine ⟨⟨by omega, by omega⟩, fun q hq hqpr hdvd => ?_⟩
    rcases (Nat.Prime.dvd_mul hqpr).1 hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hpp).1 h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hqp).1 h; omega
  set T := (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) with hT
  have hcard := Finset.card_le_card hsub
  have h3 : ((Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪ T).card
      ≤ ⌊z⌋₊ + ⌊z⌋₊ + T.card := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans ?_
    have := (Finset.card_image_le (s := Finset.Icc 1 ⌊z⌋₊) (f := fun q => s - q))
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this ⊢
    omega
  have h4 := hcard.trans h3
  have h5 : (r s : ℝ) ≤ (⌊z⌋₊ : ℝ) + ⌊z⌋₊ + S s z := by
    unfold r S; exact_mod_cast h4
  have h6 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  linarith

/-- `C s ≥ 3` for even `s`. -/
theorem n9_C_ge_three (s : ℕ) (hs : Even s) (hs0 : 0 < s) : 3 ≤ C s := by
  unfold C
  have h2 : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hs, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h2]
  have hrest : (1 : ℝ) ≤ ∏ p ∈ s.primeFactors.erase 2, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    calc (1 : ℝ) = ∏ p ∈ s.primeFactors.erase 2, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intros; norm_num
        · intro p _
          have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
          linarith
  norm_num
  linarith

noncomputable def c4_b (p : ℕ) : ℝ := ((1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 16 - 1) / p

lemma c4_b_nonneg (p : ℕ) : 0 ≤ c4_b p := by
  unfold c4_b
  apply div_nonneg _ (Nat.cast_nonneg _)
  have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
  have : 1 ≤ (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 16 := one_le_pow₀ (by linarith)
  linarith

lemma c4_b_le (p : ℕ) (hp : 37 ≤ p) :
    c4_b p ≤ 20 * (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold c4_b
  have h : (37 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ) - 1 with hqdef
  have hpq : (p : ℝ) = q + 1 := by rw [hqdef]; ring
  rw [hpq]
  have hq10 : (36 : ℝ) ≤ q := by linarith
  rw [div_le_iff₀ (by linarith)]
  have e : (1 + (q + 1) / q ^ 2) ^ 16 - 1 = ((q ^ 2 + q + 1) ^ 16 - q ^ 32) / q ^ 32 := by
    field_simp; ring
  rw [e, show 20 * (1 / q ^ 2) * (q + 1) = (20 * (q + 1) * q ^ 30) / q ^ 32 by
    field_simp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  obtain ⟨d, hd, hqd⟩ : ∃ d, 0 ≤ d ∧ q = d + 36 := ⟨q - 36, by linarith, by ring⟩
  rw [hqd]
  ring_nf
  linarith [pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5, pow_nonneg hd 6,
    pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10, pow_nonneg hd 11,
    pow_nonneg hd 12, pow_nonneg hd 13, pow_nonneg hd 14, pow_nonneg hd 15, pow_nonneg hd 16,
    pow_nonneg hd 17, pow_nonneg hd 18, pow_nonneg hd 19, pow_nonneg hd 20, pow_nonneg hd 21,
    pow_nonneg hd 22, pow_nonneg hd 23, pow_nonneg hd 24, pow_nonneg hd 25, pow_nonneg hd 26,
    pow_nonneg hd 27, pow_nonneg hd 28, pow_nonneg hd 29, pow_nonneg hd 30, pow_nonneg hd 31]

lemma c4_tail (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p ∧ 37 ≤ p) :
    ∀ m : ℕ, 35 ≤ m → (∀ p ∈ Q, p ≤ m) →
      ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 70 - 1 / (2 * (m : ℝ)) := by
  induction Q using Finset.induction_on_max with
  | empty =>
    intro m hm _
    have : (35 : ℝ) ≤ m := by exact_mod_cast hm
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
    have haR : (37 : ℝ) ≤ a := by exact_mod_cast ha.2
    have hma : (a : ℝ) ≤ m := by exact_mod_cast hle a (mem_insert_self a s)
    have key : 1 / ((a : ℝ) - 1) ^ 2 ≤ 1 / (2 * ((a : ℝ) - 2)) - 1 / (2 * (a : ℝ)) := by
      rw [div_sub_div _ _ (by nlinarith) (by nlinarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    have hm2 : 1 / (2 * (m : ℝ)) ≤ 1 / (2 * (a : ℝ)) := by
      apply one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

lemma c4_exp_le (t : ℝ) (ht : t < 1) : exp t ≤ 1 / (1 - t) := by
  have h := Real.add_one_le_exp (-t)
  rw [le_div_iff₀ (by linarith)]
  have : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

lemma c4_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ P, (1 + c4_b p) ≤ 438340 := by
  set Q := P.filter (fun p => 37 ≤ p) with hQdef
  have hsub : P ⊆ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) ∪ Q := by
    intro p hp
    obtain ⟨hpr, hp2⟩ := hP p hp
    by_cases h : 37 ≤ p
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
    · apply mem_union_left
      have := hpr.two_le
      interval_cases p <;> first | (simp; done) | exact absurd rfl hp2 | norm_num at hpr
  have hdisj : Disjoint ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) Q := by
    rw [Finset.disjoint_left]
    intro a ha haQ
    have := (mem_filter.1 haQ).2
    simp at ha; omega
  have h1 : ∏ p ∈ P, (1 + c4_b p) ≤ ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) ∪ Q, (1 + c4_b p) :=
    prod_le_prod_of_subset_of_one_le hsub (fun i _ => by linarith [c4_b_nonneg i])
      (fun i _ _ => by linarith [c4_b_nonneg i])
  rw [prod_union hdisj] at h1
  have h357 : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), (1 + c4_b p) ≤ 313100 := by
    simp [c4_b]; norm_num
  have hQodd : ∀ p ∈ Q, Odd p ∧ 37 ≤ p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(hP p hp1).1.odd_of_ne_two (hP p hp1).2, hp2⟩
  have hsum : ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 70 := by
    have := c4_tail Q hQodd (max 35 (Q.sup id)) (le_max_left _ _)
      (fun p hp => le_max_of_le_right (le_sup (f := id) hp))
    have h9 : (0 : ℝ) ≤ 1 / (2 * ((max 35 (Q.sup id) : ℕ) : ℝ)) := by positivity
    linarith
  have hbsum : ∑ p ∈ Q, c4_b p ≤ 2 / 7 := by
    calc ∑ p ∈ Q, c4_b p ≤ ∑ p ∈ Q, 20 * (1 / ((p : ℝ) - 1) ^ 2) :=
          sum_le_sum (fun p hp => c4_b_le p (hQodd p hp).2)
      _ = 20 * ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
      _ ≤ 20 * (1 / 70) := by gcongr
      _ = 2 / 7 := by norm_num
  have hQprod : ∏ p ∈ Q, (1 + c4_b p) ≤ 1 / (1 - 2 / 7) := by
    calc ∏ p ∈ Q, (1 + c4_b p) ≤ exp (∑ p ∈ Q, c4_b p) :=
          Real.prod_one_add_le_exp_sum Q c4_b_nonneg
      _ ≤ exp (2 / 7) := exp_le_exp.2 hbsum
      _ ≤ 1 / (1 - 2 / 7) := c4_exp_le _ (by norm_num)
  have hQ1 : 0 ≤ ∏ p ∈ Q, (1 + c4_b p) := prod_nonneg (fun i _ => by linarith [c4_b_nonneg i])
  calc ∏ p ∈ P, (1 + c4_b p)
      ≤ (∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), (1 + c4_b p)) * ∏ p ∈ Q, (1 + c4_b p) := h1
    _ ≤ 313100 * (1 / (1 - 2 / 7)) := by gcongr
    _ ≤ 438340 := by norm_num

lemma c4_card (N : ℕ) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ p ≠ 2) :
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

lemma c4_mul_b (p : ℕ) (hp : p ≠ 0) :
    (p : ℝ) * c4_b p = (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 16 - 1 := by
  unfold c4_b
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp

lemma c4_pointwise (N s : ℕ) (hs : s ∈ (Icc 1 N).filter Even) :
    C s ^ 16 = 43046721 * ∑ U ∈ ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).powerset,
      if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0 := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  simp only [mem_filter, mem_Icc] at hs
  obtain ⟨⟨h1, h2⟩, hev⟩ := hs
  have hs0 : s ≠ 0 := by omega
  have h2s : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hev, hs0⟩
  unfold C
  rw [← prod_pow, ← mul_prod_erase _ _ h2s]
  congr 1
  · norm_num
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
  have hp0 : p ≠ 0 := (mem_filter.1 hp).2.1.ne_zero
  split_ifs
  · rw [c4_mul_b p hp0]; ring
  · simp

/-- Sixteenth moment: `∑_{s ≤ x, s even} C(s)^16 ≤ 9440000000000 x`. -/
theorem c4_mean (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (C s) ^ 16 ≤ 9440000000000 * x := by
  set N := ⌊x⌋₊
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.1 hp).2
  set E := (Icc 1 N).filter Even
  rw [sum_congr rfl (fun s hs => c4_pointwise N s hs), ← mul_sum, sum_comm]
  have hterm : ∀ U ∈ P.powerset,
      ∑ s ∈ E, (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0)
        ≤ x / 2 * ∏ p ∈ U, c4_b p := by
    intro U hU
    have hUP : ∀ p ∈ U, p.Prime ∧ p ≠ 2 := fun p hp => hP p (mem_powerset.1 hU hp)
    rw [← sum_filter, sum_const, nsmul_eq_mul, prod_mul_distrib]
    have hc := c4_card N U hUP
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
    have hb : 0 ≤ ∏ p ∈ U, c4_b p := prod_nonneg (fun p _ => c4_b_nonneg p)
    calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, c4_b p)
        ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, c4_b p) := by
          gcongr
      _ = x / 2 * ∏ p ∈ U, c4_b p := by field_simp
  calc 43046721 * ∑ U ∈ P.powerset, ∑ s ∈ E,
        (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0)
      ≤ 43046721 * ∑ U ∈ P.powerset, x / 2 * ∏ p ∈ U, c4_b p := by
        gcongr with U hU; exact hterm U hU
    _ = 43046721 * (x / 2) * ∏ p ∈ P, (1 + c4_b p) := by
        rw [prod_one_add, mul_sum, mul_sum]; simp only [mul_assoc]
    _ ≤ 43046721 * (x / 2) * 438340 := by gcongr; exact c4_prod P hP
    _ ≤ 9440000000000 * x := by nlinarith

/-- `(∑ f)^4 ≤ |F|^3 ∑ f^4` (Cauchy–Schwarz twice). -/
theorem n9_holder (F : Finset ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ F, f s) ^ 4 ≤ (F.card : ℝ) ^ 3 * ∑ s ∈ F, f s ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := F) (f := f)
  have h2 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun s => f s ^ 2)
  have h0 : 0 ≤ (∑ s ∈ F, f s) ^ 2 := sq_nonneg _
  have h3 : ((∑ s ∈ F, f s) ^ 2) ^ 2 ≤ ((F.card : ℝ) * ∑ s ∈ F, f s ^ 2) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have e1 : (∑ s ∈ F, f s) ^ 4 = ((∑ s ∈ F, f s) ^ 2) ^ 2 := by ring
  have e2 : ∑ s ∈ F, f s ^ 4 = ∑ s ∈ F, (f s ^ 2) ^ 2 := by
    apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2]
  calc ((∑ s ∈ F, f s) ^ 2) ^ 2 ≤ ((F.card : ℝ) * ∑ s ∈ F, f s ^ 2) ^ 2 := h3
    _ = (F.card : ℝ) ^ 2 * (∑ s ∈ F, f s ^ 2) ^ 2 := by ring
    _ ≤ (F.card : ℝ) ^ 2 * ((F.card : ℝ) * ∑ s ∈ F, (f s ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- `(∑ f)^8 ≤ |F|^7 ∑ f^8`. -/
theorem n9_holder8 (F : Finset ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ F, f s) ^ 8 ≤ (F.card : ℝ) ^ 7 * ∑ s ∈ F, f s ^ 8 := by
  have h1 := n9_holder F f
  have h2 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun s => f s ^ 4)
  have h0 : 0 ≤ (∑ s ∈ F, f s) ^ 4 := by
    have : (∑ s ∈ F, f s) ^ 4 = ((∑ s ∈ F, f s) ^ 2) ^ 2 := by ring
    rw [this]; positivity
  have h3 : ((∑ s ∈ F, f s) ^ 4) ^ 2 ≤ ((F.card : ℝ) ^ 3 * ∑ s ∈ F, f s ^ 4) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have e1 : (∑ s ∈ F, f s) ^ 8 = ((∑ s ∈ F, f s) ^ 4) ^ 2 := by ring
  have e2 : ∑ s ∈ F, f s ^ 8 = ∑ s ∈ F, (f s ^ 4) ^ 2 := by
    apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2]
  calc ((∑ s ∈ F, f s) ^ 4) ^ 2 ≤ ((F.card : ℝ) ^ 3 * ∑ s ∈ F, f s ^ 4) ^ 2 := h3
    _ = (F.card : ℝ) ^ 6 * (∑ s ∈ F, f s ^ 4) ^ 2 := by ring
    _ ≤ (F.card : ℝ) ^ 6 * ((F.card : ℝ) * ∑ s ∈ F, (f s ^ 4) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- `(∑ f)^16 ≤ |F|^15 ∑ f^16`. -/
theorem n9_holder16 (F : Finset ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ F, f s) ^ 16 ≤ (F.card : ℝ) ^ 15 * ∑ s ∈ F, f s ^ 16 := by
  have h1 := n9_holder8 F f
  have h2 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun s => f s ^ 8)
  have h0 : 0 ≤ (∑ s ∈ F, f s) ^ 8 := by
    have : (∑ s ∈ F, f s) ^ 8 = ((∑ s ∈ F, f s) ^ 4) ^ 2 := by ring
    rw [this]; positivity
  have h3 : ((∑ s ∈ F, f s) ^ 8) ^ 2 ≤ ((F.card : ℝ) ^ 7 * ∑ s ∈ F, f s ^ 8) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have e1 : (∑ s ∈ F, f s) ^ 16 = ((∑ s ∈ F, f s) ^ 8) ^ 2 := by ring
  have e2 : ∑ s ∈ F, f s ^ 16 = ∑ s ∈ F, (f s ^ 8) ^ 2 := by
    apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2]
  calc ((∑ s ∈ F, f s) ^ 8) ^ 2 ≤ ((F.card : ℝ) ^ 7 * ∑ s ∈ F, f s ^ 8) ^ 2 := h3
    _ = (F.card : ℝ) ^ 14 * (∑ s ∈ F, f s ^ 8) ^ 2 := by ring
    _ ≤ (F.card : ℝ) ^ 14 * ((F.card : ℝ) * ∑ s ∈ F, (f s ^ 8) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end P85

-- ===== Large =====
/-! Large range `n ≥ e^7000`: the `241` argument with Chebyshev's constant `a ≈ 0.9212` (`psi_lower`). -/

open Finset Real

namespace P85
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

/-- Per-term bound: `(L(t) - L(t-1)) · (log t)^2 / t ≥ 0.8482` for `t ≥ e^6960`. -/
lemma term_lower (t : ℝ) (ht : exp 6960 ≤ t) :
    8482 / 10000 ≤ (Lf t - Lf (t - 1)) * (log t ^ 2 / t) := by
  have hbig : (10 : ℝ) ^ 12 ≤ t := (exp99_ge 6960 (by norm_num)).trans ht
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  set u := log t with hu_def
  set v := log (t - 1) with hv_def
  have hu : 6960 ≤ u := by
    have := log_le_log (exp_pos 6960) ht
    rwa [log_exp] at this
  have hvu : v ≤ u := log_le_log ht1 (by linarith)
  have huv : u - v ≤ 1 / (t - 1) := by
    have h := log_le_sub_one_of_pos (show 0 < t / (t - 1) by positivity)
    rw [log_div (by linarith) ht1.ne'] at h
    have : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  have hinv : 1 / (t - 1) ≤ 1 := by
    rw [div_le_one ht1]; linarith
  have hv : 6959 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  have hsq : u ^ 2 - v ^ 2 ≤ 2 * u / (t - 1) := by
    have : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [this]
    calc (u - v) * (u + v) ≤ 1 / (t - 1) * (u + v) :=
          mul_le_mul_of_nonneg_right huv (by linarith)
      _ ≤ 1 / (t - 1) * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * u / (t - 1) := by ring
  have huv2 : u / v ^ 2 ≤ 1 / 6900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hratio : u ^ 2 / v ^ 2 ≤ 1 + 2 / 6900 / (t - 1) := by
    have e : u ^ 2 / v ^ 2 = 1 + (u ^ 2 - v ^ 2) / v ^ 2 := by field_simp; ring
    rw [e]
    have : (u ^ 2 - v ^ 2) / v ^ 2 ≤ 2 * u / (t - 1) / v ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e2 : 2 * u / (t - 1) / v ^ 2 = 2 * (u / v ^ 2) / (t - 1) := by field_simp
    have : 2 * (u / v ^ 2) / (t - 1) ≤ 2 * (1 / 6900) / (t - 1) :=
      div_le_div_of_nonneg_right (by linarith) ht1.le
    have e3 : 2 * (1 / 6900) / (t - 1) = 2 / 6900 / (t - 1) := by ring
    linarith
  set g := (t - 1 - 10 ^ 6) * (t - 1 - 3000001) with hg
  have hg0 : 0 ≤ g := by rw [hg]; apply mul_nonneg <;> linarith
  have hgle : g ≤ (t - 1) ^ 2 := by rw [hg]; nlinarith
  have hexp : (Lf t - Lf (t - 1)) * (u ^ 2 / t)
      = 0.9211 ^ 2 / 2 * ((t - 10 ^ 6) * (t - 3000001) - g * (u ^ 2 / v ^ 2)) / t := by
    rw [Lf, Lf, ← hu_def, ← hv_def, hg]
    field_simp
  rw [hexp]
  have hgr : g * (u ^ 2 / v ^ 2) ≤ g + 2 / 6900 * (t - 1) := by
    calc g * (u ^ 2 / v ^ 2) ≤ g * (1 + 2 / 6900 / (t - 1)) := mul_le_mul_of_nonneg_left hratio hg0
      _ = g + 2 / 6900 * (g / (t - 1)) := by ring
      _ ≤ g + 2 / 6900 * (t - 1) := by
        have : g / (t - 1) ≤ t - 1 := by
          rw [div_le_iff₀ ht1]; nlinarith
        linarith
  rw [le_div_iff₀ (by linarith)]
  have e4 : (t - 10 ^ 6) * (t - 3000001) = g + 2 * t - 4000002 := by rw [hg]; ring
  rw [e4]
  nlinarith

/-- `log L ≤ L / 770` for `L ≥ 6960`. -/
theorem log_le_big (L : ℝ) (hL : 6960 ≤ L) : log L ≤ L / 770 := by
  have h6 : log 6960 ≤ 885 / 100 := by
    rw [log_le_iff_le_exp (by norm_num)]
    exact (exp_ge_poly _ (by norm_num)).trans' (by norm_num)
  have h1 : log (L / 6960) ≤ L / 6960 - 1 := log_le_sub_one_of_pos (by positivity)
  rw [log_div (by positivity) (by norm_num)] at h1
  linarith

/-- Sieve bound at the threshold `e^6960`: `r(s) ≤ 8.13 C(s) s / log² s`. -/
theorem pointwise (s : ℕ) (hs : Even s) (hbig : exp 6960 ≤ s) :
    (r s : ℝ) ≤ 813 / 100 * C s * s / (log s) ^ 2 := by
  have hs1 : (6961 : ℝ) ≤ s := by
    have := add_one_le_exp 6960; linarith
  have hs0 : 0 < s := by exact_mod_cast (show (0:ℝ) < s by linarith)
  have hspos : (0 : ℝ) < s := by linarith
  set L := log s with hLdef
  have hL : 6960 ≤ L := by
    have := log_le_log (exp_pos 6960) hbig
    rwa [log_exp] at this
  have hLpos : 0 < L := by linarith
  have hlogL := log_le_big L hL
  have hlogL' : 1 ≤ log L := by
    rw [le_log_iff_exp_le hLpos]
    have := exp_one_lt_d9; linarith
  set z := √(s : ℝ) / L ^ 3 with hzdef
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.2 hspos
  have hzpos : 0 < z := by positivity
  have hlogz : log z = L / 2 - 3 * log L := by
    rw [hzdef, log_div hsq.ne' (by positivity), Real.log_sqrt hspos.le, log_pow]
    push_cast; ring
  have hlz1 : 4961 / 10000 * L ≤ log z := by rw [hlogz]; linarith
  have hlz2 : 1 + log z ≤ L / 2 := by rw [hlogz]; linarith
  have hz1 : 1 < z := by
    have : 0 < log z := by nlinarith
    exact (log_pos_iff hzpos.le).1 this
  have hC := n9_C_ge_three s hs hs0
  have hSi := sieve_ineq s hs hs0 z hz1
  have hG := G_lower s hs hs0 z hz1
  have hrS := n9_r_le_S s z hzpos.le
  have hlzpos : 0 < log z := by nlinarith
  have hGpos : 0 < G s z := lt_of_lt_of_le (by positivity) hG
  -- `s / G ≤ 2 C s / (log z)^2 ≤ 8.0774 C s / L^2`
  have hA : (s : ℝ) / G s z ≤ 8127 / 1000 * C s * s / L ^ 2 := by
    rw [div_le_div_iff₀ hGpos (by positivity)]
    have h1 : (log z) ^ 2 ≤ 2 * C s * G s z := by
      rw [div_le_iff₀ (by positivity)] at hG; linarith
    have h2 : (4961 / 10000) ^ 2 * L ^ 2 ≤ (log z) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlz1 2
      nlinarith
    have : L ^ 2 ≤ 8127 / 1000 * C s * G s z := by nlinarith
    nlinarith
  have hzsq : z ^ 2 = s / L ^ 6 := by
    rw [hzdef, div_pow, Real.sq_sqrt hspos.le]; ring
  have hB : z ^ 2 * (1 + log z) ^ 2 ≤ s / (4 * L ^ 4) := by
    rw [hzsq]
    have h0 : 0 ≤ 1 + log z := by linarith
    have : (1 + log z) ^ 2 ≤ (L / 2) ^ 2 := pow_le_pow_left₀ h0 hlz2 2
    calc (s : ℝ) / L ^ 6 * (1 + log z) ^ 2 ≤ s / L ^ 6 * (L / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = s / (4 * L ^ 4) := by field_simp; ring
  -- `√s = e^{L/2} ≥ (L/2)^3/6 ≥ 8 L`
  have hsqrt : √(s : ℝ) = exp (L / 2) := by
    rw [exp_half, hLdef, exp_log hspos]
  have h8 : 8 * L ≤ √(s : ℝ) := by
    rw [hsqrt]
    have := pow_div_factorial_le_exp (x := L / 2) (by linarith) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have hD : 2 * z ≤ s / (4 * L ^ 4) := by
    have e : 2 * z = (8 * L) * √(s : ℝ) / (4 * L ^ 4) := by rw [hzdef]; field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc (8 * L) * √(s : ℝ) ≤ √(s : ℝ) * √(s : ℝ) := mul_le_mul_of_nonneg_right h8 hsq.le
      _ = s := Real.mul_self_sqrt hspos.le
  have hfin : (8127 / 1000 * C s * s / L ^ 2) + s / (4 * L ^ 4) + s / (4 * L ^ 4)
      ≤ 813 / 100 * C s * s / L ^ 2 := by
    rw [← sub_nonneg]
    have : 813 / 100 * C s * s / L ^ 2 - ((8127 / 1000 * C s * s / L ^ 2) + s / (4 * L ^ 4)
      + s / (4 * L ^ 4)) = (3 / 1000 * C s - 1 / (2 * L ^ 2)) * s / L ^ 2 := by
        field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg _ hspos.le
    have : 1 / (2 * L ^ 2) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  linarith

/-- Weighted first moment: `W(n) ≥ 0.8481 n` for `n ≥ e^7000`. -/
theorem W_lower (n : ℕ) (hn : exp 7000 ≤ n) :
    8481 / 10000 * (n : ℝ) ≤ ∑ s ∈ Ioc ⌊exp 6960⌋₊ n, (r s : ℝ) * (log s ^ 2 / s) := by
  set n0 := ⌊exp 6960⌋₊ with hn0def
  have hE : (10 : ℝ) ^ 12 ≤ exp 6960 := exp99_ge 6960 (by norm_num)
  have hE3 : (10 : ℝ) ^ 17 ≤ exp 40 := (exp_ge_poly 40 (by norm_num)).trans' (by norm_num)
  have hn0 : (n0 : ℝ) ≤ exp 6960 := Nat.floor_le (exp_pos _).le
  have hn0' : exp 6960 < n0 + 1 := Nat.lt_floor_add_one _
  have hexp2 : exp 7000 = exp 6960 * exp 40 := by
    rw [← exp_add]; norm_num
  have hn1 : (n : ℝ) ≥ 10 ^ 17 * exp 6960 := by
    have := mul_le_mul_of_nonneg_left hE3 (exp_pos 6960).le
    linarith
  have hnn0 : n0 ≤ n := by
    have : (n0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hbig : ∀ k : ℕ, n0 < k → exp 6960 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have habel := s6_abel (fun s => (r s : ℝ)) (fun s => log s ^ 2 / s) (fun s => Lf s) n0
    (by
      intro k hk
      have := s6_w_anti k ((exp_le_exp.2 (by norm_num : (130 : ℝ) ≤ 6960)).trans (hbig k hk))
      push_cast; exact this)
    (by
      intro k hk
      have h1 := hbig k hk
      have : ((10 ^ 6 : ℕ) : ℝ) ≤ k := by push_cast; linarith
      exact first_moment k (by exact_mod_cast this))
    n hnn0
  -- (i) main sum
  have hi : 8482 / 10000 * ((n : ℝ) - n0) ≤
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
      ≤ 2 * 6961 ^ 2 * exp 6960 := by
    have hn0big : (3000001 : ℝ) ≤ n0 := by
      have : (3000002 : ℝ) ≤ exp 6960 := by linarith
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
    have hlogm : log m ≤ 6961 := by
      rw [log_le_iff_le_exp hm0]
      have : exp 6961 = exp 6960 * exp 1 := by rw [← exp_add]; norm_num
      have h2 : (2 : ℝ) ≤ exp 1 := by have := add_one_le_exp (1 : ℝ); linarith
      nlinarith
    have hlogm0 : 0 ≤ log m := log_nonneg (by linarith)
    have hw0 : 0 ≤ log m ^ 2 / m := by positivity
    calc (∑ s ∈ range (n0 + 1), (r s : ℝ) - Lf n0) * (log m ^ 2 / m)
        ≤ m ^ 2 * (log m ^ 2 / m) := mul_le_mul_of_nonneg_right (by linarith) hw0
      _ = m * log m ^ 2 := by field_simp
      _ ≤ (2 * exp 6960) * 6961 ^ 2 := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ hlogm0 hlogm 2) (by positivity) (by positivity)
      _ = 2 * 6961 ^ 2 * exp 6960 := by ring
  push_cast at hii hiii habel
  linarith


/-- Support bound: `R(n) ≥ n / 83` for `n ≥ e^7000`. -/
theorem R_large (n : ℕ) (hn : exp 7000 ≤ n) :
    (n : ℝ) / 83 ≤ (((range (n + 1)).filter (fun s => 0 < r s)).card : ℝ) := by
  set n0 := ⌊exp 6960⌋₊ with hn0def
  have hn0' : exp 6960 < n0 + 1 := Nat.lt_floor_add_one _
  have hbig : ∀ k : ℕ, n0 < k → exp 6960 ≤ k := by
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
  have hH := n9_holder16 F (fun s => (r s : ℝ) * (log s ^ 2 / s))
  have hterm : ∀ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 16 ≤ (813 / 100) ^ 16 * C s ^ 16 := by
    intro s hs
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
    have heven : Even s := by
      by_contra h
      have := s6_r_odd s h
      omega
    have h1 := hbig s hs.1.1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (exp_pos _) h1
    have hlog : 0 < log s := log_pos (by nlinarith [add_one_le_exp (6960 : ℝ)])
    have hpb := pointwise s heven h1
    have hup : (r s : ℝ) * (log s ^ 2 / s) ≤ 813 / 100 * C s := by
      have hw : 0 < log s ^ 2 / s := by positivity
      calc (r s : ℝ) * (log s ^ 2 / s) ≤ 813 / 100 * C s * s / log s ^ 2 * (log s ^ 2 / s) :=
            mul_le_mul_of_nonneg_right hpb hw.le
        _ = 813 / 100 * C s := by field_simp
    have hlo : 0 ≤ (r s : ℝ) * (log s ^ 2 / s) := by positivity
    calc ((r s : ℝ) * (log s ^ 2 / s)) ^ 16 ≤ (813 / 100 * C s) ^ 16 := pow_le_pow_left₀ hlo hup 16
      _ = (813 / 100) ^ 16 * C s ^ 16 := by ring
  have hsumC : ∑ s ∈ F, C s ^ 16 ≤ 9440000000000 * (n : ℝ) := by
    have := c4_mean (n : ℝ) (Nat.cast_nonneg n)
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
  have hq : ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 16 ≤ (813 / 100) ^ 16 * (9440000000000 * (n : ℝ)) := by
    calc _ ≤ ∑ s ∈ F, (813 / 100) ^ 16 * C s ^ 16 := Finset.sum_le_sum hterm
      _ = (813 / 100) ^ 16 * ∑ s ∈ F, C s ^ 16 := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  rw [← hWF] at hH
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hW4 : (8481 / 10000 * (n : ℝ)) ^ 16 ≤ (∑ s ∈ Ioc n0 n, (r s : ℝ) * (log s ^ 2 / s)) ^ 16 :=
    pow_le_pow_left₀ (by positivity) hW 16
  have hq0 : 0 ≤ ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 16 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (exp_pos _) hn
  have key : (8481 / 10000 * (n : ℝ)) ^ 16 ≤ (R.card : ℝ) ^ 15 * ((813 / 100) ^ 16 * (9440000000000 * (n : ℝ))) := by
    calc _ ≤ _ := hW4
      _ ≤ _ := hH
      _ ≤ (R.card : ℝ) ^ 15 * ∑ s ∈ F, ((r s : ℝ) * (log s ^ 2 / s)) ^ 16 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hFR' 15) hq0
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  by_contra hcon
  push Not at hcon
  have hc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have h3 : (R.card : ℝ) ^ 15 ≤ ((n : ℝ) / 83) ^ 15 := pow_le_pow_left₀ hc0 hcon.le 15
  have h4 : (R.card : ℝ) ^ 15 * ((813 / 100) ^ 16 * (9440000000000 * (n : ℝ)))
      ≤ ((n : ℝ) / 83) ^ 15 * ((813 / 100) ^ 16 * (9440000000000 * (n : ℝ))) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : ((n : ℝ) / 83) ^ 15 * ((813 / 100) ^ 16 * (9440000000000 * (n : ℝ))) < (8481 / 10000 * (n : ℝ)) ^ 16 := by
    have hn4 : 0 < (n : ℝ) ^ 16 := by positivity
    have e1 : ((n : ℝ) / 83) ^ 15 * ((813 / 100) ^ 16 * (9440000000000 * (n : ℝ)))
        = (813 / 100) ^ 16 * 9440000000000 / 83 ^ 15 * (n : ℝ) ^ 16 := by ring
    have e2 : (8481 / 10000 * (n : ℝ)) ^ 16 = (8481 / 10000) ^ 16 * (n : ℝ) ^ 16 := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_right (by norm_num) hn4
  linarith


end P85

-- ===== Final =====
/-! Density `σ(A) ≥ 1/42`, Mann's theorem, and the `85` goal. -/

open Finset Real

namespace P85
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
/-- `σ(A) ≥ 1/42`. -/
theorem density_A : (1 : ℝ) / 42 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 420
  · by_cases h10 : 10 ≤ N
    · have h1 : Icc 1 10 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, n9_small_mem_A a ha.1 ha.2⟩
      have h2 := card_le_card h1
      have h3' : (10 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 420 := by exact_mod_cast hsmall
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
  have hN' : (421 : ℝ) ≤ N := by exact_mod_cast hsmall
  have hL := s6d_large N
  have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
      ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
  have hy6 : (0 : ℝ) < ((2 * N + 6 : ℕ) : ℝ) := by push_cast; linarith
  by_cases hbig : exp 7000 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := R_large _ hbig
    have hx := exp99_ge 7000 (by norm_num)
    push_cast at hR hbig
    linarith
  push Not at hbig
  by_cases hmid : 76 ≤ log ((2 * N + 6 : ℕ) : ℝ)
  · have hlog : log ((2 * N + 6 : ℕ) : ℝ) ≤ 7000 := by
      rw [log_le_iff_le_exp hy6]; exact hbig.le
    have hR := rv_range _ hmid hlog
    have hx : exp 76 ≤ ((2 * N + 6 : ℕ) : ℝ) := by
      rw [← exp_log hy6]; exact exp_le_exp.2 hmid
    have hx' := exp99_ge 76 (by norm_num)
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
      have hlog : log ((2 * N + 3 : ℕ) : ℝ) < 76 := by linarith
      have hmul : (Nat.primeCounting (2 * N + 3) : ℝ) * log ((2 * N + 3 : ℕ) : ℝ) ≤
          (Nat.primeCounting (2 * N + 3) : ℝ) * 76 :=
        mul_le_mul_of_nonneg_left hlog.le hpi0
      have hlog5 : 5 * log ((2 * N + 3 : ℕ) : ℝ) ≤ 5 * 76 := by linarith
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
theorem n9_all (t : ℕ) : s6m_P 84 t := by
  have hA := density_A
  have hk : (1 : ℝ) ≤ ((42 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 42 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd `n ≥ 171` is a sum of exactly `85` primes. -/
theorem exact_85 (n : ℕ) (hodd : Odd n) (hn : 171 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 85 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 255 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all ((n - 255) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 170) 3 + Multiset.replicate (255 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end P85

/-- The campaign goal (platform theorem `odd_sum_le_85_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 85 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 171 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := P85.exact_85 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

