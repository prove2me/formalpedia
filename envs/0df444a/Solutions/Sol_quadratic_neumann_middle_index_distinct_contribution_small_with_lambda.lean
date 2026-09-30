-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:45:00.350059+00:00
-- url     : https://prove2.me/submissions/2f252dd9-ecee-43d8-86f2-97960a05daac

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_middle_index_distinct_bound_from_centered_and_mean_bounds
import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
import Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_as_coefficient_sum
import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound
import Theorems.Thm_sign_matrix_frobenius_norm_le_sqrt_rank

open MatrixCompletion

/-!
# The `ω₁ = ω₃ ≠ ω₂` quadratic Neumann contribution is `O(λ^{-3/2})`

We split the contribution into its centered and mean parts (`ξ² = (1-2p)ξ + p(1-p)`).
The centered part is handled by the platform theorem
`quadratic_neumann_middle_index_distinct_centered_contribution_small_with_lambda`.
For the mean part we use the natural two-term Bernstein tail for the scalar
coefficients `H_ω = matrixEntrySum (p⁻¹(P_Ω - p I) B_ω)` at the shifted level `β + 2`,
a union bound over the `n₁ n₂` indices, the identity
`Mean = p⁻¹(1-p) Σ_ω E_ω H_ω e_ω`, `‖E‖_F ≤ √r`, and an explicit scale computation
showing that the resulting bound is at most `2(Cfro + Centry) λ^{-3/2}` under the
sample-size hypothesis `m ≥ λ μ₀^{4/3} n r^{4/3} β log n` (for `n ≥ 2`).
-/


theorem rpow_three_halves_sq' {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rpow_four_thirds_cube' {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((4 : ℝ) / 3)) ^ 3 = x ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rpow_neg_three_halves_sq' {x : ℝ} (hx : 0 < x) :
    (x ^ (-((3 : ℝ) / 2))) ^ 2 = (x ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

theorem rpow_four_thirds_pow_four_ge_five {x : ℝ} (hx : 1 ≤ x) :
    x ^ 5 ≤ (x ^ ((4 : ℝ) / 3)) ^ 4 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (x ^ ((4 : ℝ) / 3)) ^ 4 = x ^ ((16 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  have h2 : x ^ 5 = x ^ ((5 : ℕ) : ℝ) := (Real.rpow_natCast x 5).symm
  rw [h1, h2]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem rpow_four_thirds_pow_four_ge_four {x : ℝ} (hx : 1 ≤ x) :
    x ^ 4 ≤ (x ^ ((4 : ℝ) / 3)) ^ 4 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (x ^ ((4 : ℝ) / 3)) ^ 4 = x ^ ((16 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  have h2 : x ^ 4 = x ^ ((4 : ℕ) : ℝ) := (Real.rpow_natCast x 4).symm
  rw [h1, h2]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem log_two_gt_069 : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

theorem scalar_key1 (β L μ₀ : ℝ) (hβ : 2 < β) (hL69 : 0.69 < L) (hμ : 1 ≤ μ₀) :
    (β + 2) * L ≤ 4 * μ₀ * β ^ 3 * L ^ 3 := by
  have hβ0 : 0 < β := by linarith
  have hL0 : 0 < L := by linarith
  have hβ2 : 4 ≤ β ^ 2 := by nlinarith [sq_nonneg (β - 2)]
  have hβ3 : 4 * β ≤ β ^ 3 := by
    have := mul_le_mul_of_nonneg_left hβ2 hβ0.le
    calc 4 * β = β * 4 := by ring
      _ ≤ β * β ^ 2 := this
      _ = β ^ 3 := by ring
  have h1 : β + 2 ≤ 1.8 * β ^ 3 := by linarith
  have h2 : (0.47 : ℝ) ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.69) hL69.le 2
    norm_num at this; linarith
  have hb3 : 0 < β ^ 3 := by positivity
  have e1 : 1.8 * β ^ 3 ≤ 4 * β ^ 3 * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 4 * β ^ 3)
    linarith
  have e2 : 4 * β ^ 3 * L ^ 2 ≤ 4 * μ₀ * β ^ 3 * L ^ 2 := by
    have h4 : 0 ≤ 4 * β ^ 3 * L ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hμ h4
    linarith
  have h3 : (β + 2) ≤ 4 * μ₀ * β ^ 3 * L ^ 2 := by linarith
  calc (β + 2) * L ≤ (4 * μ₀ * β ^ 3 * L ^ 2) * L := mul_le_mul_of_nonneg_right h3 hL0.le
    _ = 4 * μ₀ * β ^ 3 * L ^ 3 := by ring

theorem scalar_key2 (β L : ℝ) (hβ : 2 < β) (hL69 : 0.69 < L) :
    ((β + 2) * L) ^ 2 ≤ 4 * (β * L) ^ 4 := by
  have hβ0 : 0 < β := by linarith
  have hL0 : 0 < L := by linarith
  have hβL : 1 ≤ β * L := by nlinarith
  have e1 : (β + 2) ^ 2 ≤ 4 * β ^ 2 := by nlinarith
  have e2 : (β * L) ^ 2 ≤ (β * L) ^ 4 := pow_le_pow_right₀ hβL (by norm_num)
  have hL2 : 0 ≤ L ^ 2 := by positivity
  calc ((β + 2) * L) ^ 2 = (β + 2) ^ 2 * L ^ 2 := by ring
    _ ≤ 4 * β ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right e1 hL2
    _ = 4 * (β * L) ^ 2 := by ring
    _ ≤ 4 * (β * L) ^ 4 := by linarith

theorem term1_sq_identity (Cfro L' p μ₀ r N nmin m : ℝ) (hp : p = m / (N * nmin))
    (hN : 0 < N) (hnmin : 0 < nmin) (hm : 0 < m) (hμ0 : 0 ≤ μ₀) (hr0 : 0 ≤ r)
    (hL' : 0 ≤ L') :
    (Real.sqrt (L' / p) * (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2))
      * p⁻¹ * Real.sqrt r) ^ 2 = Cfro ^ 2 * (L' * μ₀ ^ 3 * r ^ 4 * N ^ 3) / m ^ 3 := by
  have hppos : 0 < p := by rw [hp]; positivity
  have hsq1 : (Real.sqrt (L' / p)) ^ 2 = L' / p := Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have hsq3 := rpow_three_halves_sq' hμ0
  have hsq4 := rpow_three_halves_sq' (show (0:ℝ) ≤ r / nmin by positivity)
  have e1 : (Real.sqrt (L' / p) * (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2))
      * p⁻¹ * Real.sqrt r) ^ 2
      = (Real.sqrt (L' / p)) ^ 2 * Cfro ^ 2 * (μ₀ ^ ((3 : ℝ) / 2)) ^ 2
        * ((r / nmin) ^ ((3 : ℝ) / 2)) ^ 2 * (p⁻¹) ^ 2 * (Real.sqrt r) ^ 2 := by ring
  rw [e1, hsq1, hsq2, hsq3, hsq4, hp]
  field_simp

theorem term2_sq_identity (Centry L' p μ₀ r N nmin m : ℝ) (hp : p = m / (N * nmin))
    (hN : 0 < N) (hnmin : 0 < nmin) (hm : 0 < m) (hr0 : 0 ≤ r) :
    (L' / p * (Centry * μ₀ ^ 2 * (r / nmin) ^ 2) * p⁻¹ * Real.sqrt r) ^ 2
      = Centry ^ 2 * (L' ^ 2 * μ₀ ^ 4 * r ^ 5 * N ^ 4) / m ^ 4 := by
  have hsq2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have e1 : (L' / p * (Centry * μ₀ ^ 2 * (r / nmin) ^ 2) * p⁻¹ * Real.sqrt r) ^ 2
      = (L' / p) ^ 2 * Centry ^ 2 * μ₀ ^ 4 * ((r / nmin) ^ 2) ^ 2 * (p⁻¹) ^ 2 * (Real.sqrt r) ^ 2 := by
    ring
  rw [e1, hsq2, hp]
  field_simp

theorem rhs_sq_identity (C lam : ℝ) (hlam : 0 < lam) :
    (2 * C * lam ^ (-((3 : ℝ) / 2))) ^ 2 = 4 * C ^ 2 * (lam ^ 3)⁻¹ := by
  have e1 : (2 * C * lam ^ (-((3 : ℝ) / 2))) ^ 2 = 4 * C ^ 2 * (lam ^ (-((3 : ℝ) / 2))) ^ 2 := by
    ring
  rw [e1, rpow_neg_three_halves_sq' hlam]

theorem final_div_step (C X lam m : ℝ) (k : ℕ) (hlam : 0 < lam) (hm : 0 < m)
    (hgoal : lam ^ 3 * X ≤ 4 * m ^ k) :
    C ^ 2 * X / m ^ k ≤ 4 * C ^ 2 * (lam ^ 3)⁻¹ := by
  have hmk : 0 < m ^ k := by positivity
  have hlam3 : 0 < lam ^ 3 := by positivity
  rw [div_le_iff₀ hmk]
  calc C ^ 2 * X = C ^ 2 * (lam ^ 3 * X) * (lam ^ 3)⁻¹ := by field_simp
    _ ≤ C ^ 2 * (4 * m ^ k) * (lam ^ 3)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hgoal (by positivity)
    _ = 4 * C ^ 2 * (lam ^ 3)⁻¹ * m ^ k := by ring

/-- First (Frobenius) Bernstein term times the prefactor `p⁻¹ √r`. -/
theorem term1_bound (Cfro β L lam μ₀ r N nmin m p : ℝ)
    (hCfro : 0 < Cfro) (hβ : 2 < β) (hL : Real.log 2 ≤ L)
    (hlam : 1 ≤ lam) (hμ : 1 ≤ μ₀) (hr : 1 ≤ r) (hN : 0 < N) (hnmin : 0 < nmin)
    (hm : lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) ≤ m)
    (hp : p = m / (N * nmin)) :
    Real.sqrt (((β + 2) * L) / p) *
        (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2)) *
        p⁻¹ * Real.sqrt r
      ≤ 2 * Cfro * lam ^ (-((3 : ℝ) / 2)) := by
  subst hp
  have hL69 : (0.69 : ℝ) < L := lt_of_lt_of_le log_two_gt_069 hL
  have hL0 : 0 < L := by linarith
  have hβ0 : 0 < β := by linarith
  have hlam0 : 0 < lam := by linarith
  have hμ0 : 0 < μ₀ := by linarith
  have hr0 : 0 < r := by linarith
  have hm₀pos : 0 < lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le hm₀pos hm
  have hB : 0 ≤ 2 * Cfro * lam ^ (-((3 : ℝ) / 2)) := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero hB
  rw [term1_sq_identity Cfro ((β + 2) * L) (m / (N * nmin)) μ₀ r N nmin m rfl hN hnmin hmpos
    hμ0.le hr0.le (by positivity), rhs_sq_identity Cfro lam hlam0]
  apply final_div_step Cfro _ lam m 3 hlam0 hmpos
  have hm3 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3 ≤ m ^ 3 :=
    pow_le_pow_left₀ hm₀pos.le hm 3
  have hm₀3 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3
      = lam ^ 3 * μ₀ ^ 4 * N ^ 3 * r ^ 4 * (β * L) ^ 3 := by
    rw [← rpow_four_thirds_cube' hμ0.le, ← rpow_four_thirds_cube' hr0.le]; ring
  have hkey := scalar_key1 β L μ₀ hβ hL69 hμ
  calc lam ^ 3 * ((β + 2) * L * μ₀ ^ 3 * r ^ 4 * N ^ 3)
      ≤ lam ^ 3 * ((4 * μ₀ * β ^ 3 * L ^ 3) * μ₀ ^ 3 * r ^ 4 * N ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 4 * (lam ^ 3 * μ₀ ^ 4 * N ^ 3 * r ^ 4 * (β * L) ^ 3) := by ring
    _ = 4 * (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3 := by rw [hm₀3]
    _ ≤ 4 * m ^ 3 := by linarith

/-- Second (sup-norm) Bernstein term times the prefactor `p⁻¹ √r`. -/
theorem term2_bound (Centry β L lam μ₀ r N nmin m p : ℝ)
    (hCentry : 0 < Centry) (hβ : 2 < β) (hL : Real.log 2 ≤ L)
    (hlam : 1 ≤ lam) (hμ : 1 ≤ μ₀) (hr : 1 ≤ r) (hN : 0 < N) (hnmin : 0 < nmin)
    (hm : lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) ≤ m)
    (hp : p = m / (N * nmin)) :
    (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * ((r / nmin) ^ 2)) *
        p⁻¹ * Real.sqrt r
      ≤ 2 * Centry * lam ^ (-((3 : ℝ) / 2)) := by
  subst hp
  have hL69 : (0.69 : ℝ) < L := lt_of_lt_of_le log_two_gt_069 hL
  have hL0 : 0 < L := by linarith
  have hβ0 : 0 < β := by linarith
  have hlam0 : 0 < lam := by linarith
  have hμ0 : 0 < μ₀ := by linarith
  have hr0 : 0 < r := by linarith
  have hm₀pos : 0 < lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le hm₀pos hm
  have hB : 0 ≤ 2 * Centry * lam ^ (-((3 : ℝ) / 2)) := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero hB
  rw [term2_sq_identity Centry ((β + 2) * L) (m / (N * nmin)) μ₀ r N nmin m rfl hN hnmin hmpos
    hr0.le, rhs_sq_identity Centry lam hlam0]
  apply final_div_step Centry _ lam m 4 hlam0 hmpos
  have hm4 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 4 ≤ m ^ 4 :=
    pow_le_pow_left₀ hm₀pos.le hm 4
  have hm₀4 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 4
      = lam ^ 4 * (μ₀ ^ ((4 : ℝ) / 3)) ^ 4 * N ^ 4 * (r ^ ((4 : ℝ) / 3)) ^ 4 * (β * L) ^ 4 := by
    ring
  have hbig : lam ^ 3 * μ₀ ^ 4 * N ^ 4 * r ^ 5 * (β * L) ^ 4
      ≤ lam ^ 4 * (μ₀ ^ ((4 : ℝ) / 3)) ^ 4 * N ^ 4 * (r ^ ((4 : ℝ) / 3)) ^ 4 * (β * L) ^ 4 := by
    have e1 : lam ^ 3 ≤ lam ^ 4 := pow_le_pow_right₀ hlam (by norm_num)
    have e2 := rpow_four_thirds_pow_four_ge_four hμ
    have e3 := rpow_four_thirds_pow_four_ge_five hr
    have hN4 : 0 ≤ N ^ 4 := by positivity
    have hβL4 : 0 ≤ (β * L) ^ 4 := by positivity
    apply mul_le_mul_of_nonneg_right _ hβL4
    apply mul_le_mul _ e3 (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ hN4
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  have hkey := scalar_key2 β L hβ hL69
  calc lam ^ 3 * (((β + 2) * L) ^ 2 * μ₀ ^ 4 * r ^ 5 * N ^ 4)
      ≤ lam ^ 3 * ((4 * (β * L) ^ 4) * μ₀ ^ 4 * r ^ 5 * N ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 4 * (lam ^ 3 * μ₀ ^ 4 * N ^ 4 * r ^ 5 * (β * L) ^ 4) := by ring
    _ ≤ 4 * (lam ^ 4 * (μ₀ ^ ((4 : ℝ) / 3)) ^ 4 * N ^ 4 * (r ^ ((4 : ℝ) / 3)) ^ 4 * (β * L) ^ 4) := by
        linarith
    _ = 4 * (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 4 := by rw [hm₀4]
    _ ≤ 4 * m ^ 4 := by linarith

/-- Combined: the Bernstein scale times `p⁻¹ √r` is `O(λ^{-3/2})`. -/
theorem mean_scale_bound (Cfro Centry β L lam μ₀ r N nmin m p : ℝ)
    (hCfro : 0 < Cfro) (hCentry : 0 < Centry) (hβ : 2 < β) (hL : Real.log 2 ≤ L)
    (hlam : 1 ≤ lam) (hμ : 1 ≤ μ₀) (hr : 1 ≤ r) (hN : 0 < N) (hnmin : 0 < nmin)
    (hm : lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) ≤ m)
    (hp : p = m / (N * nmin)) :
    (Real.sqrt (((β + 2) * L) / p) *
        (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2)) +
      (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * ((r / nmin) ^ 2))) *
        p⁻¹ * Real.sqrt r
      ≤ 2 * (Cfro + Centry) * lam ^ (-((3 : ℝ) / 2)) := by
  have h1 := term1_bound Cfro β L lam μ₀ r N nmin m p hCfro hβ hL hlam hμ hr hN hnmin hm hp
  have h2 := term2_bound Centry β L lam μ₀ r N nmin m p hCentry hβ hL hlam hμ hr hN hnmin hm hp
  have e : (Real.sqrt (((β + 2) * L) / p) *
        (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2)) +
      (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * ((r / nmin) ^ 2))) *
        p⁻¹ * Real.sqrt r
      = Real.sqrt (((β + 2) * L) / p) *
        (Cfro * μ₀ ^ ((3 : ℝ) / 2) * (r / nmin) ^ ((3 : ℝ) / 2)) *
        p⁻¹ * Real.sqrt r +
        (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * ((r / nmin) ^ 2)) *
        p⁻¹ * Real.sqrt r := by ring
  rw [e]
  linarith

/-! ## Degenerate case `n₁ = n₂ = 1` -/

theorem mc_contribution_zero_of_subsingleton {n1 n2 r : ℕ} {M : Matrix (Fin n1) (Fin n2) ℝ}
    [Subsingleton (Fin n1 × Fin n2)] (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : ℝ) : quadraticNeumannMiddleIndexDistinctContribution Omega S p = 0 := by
  unfold quadraticNeumannMiddleIndexDistinctContribution
  rw [Finset.sum_eq_zero]
  · simp
  intro w1 _
  rw [Finset.sum_eq_zero]
  intro w2 _
  rw [if_pos (Subsingleton.elim w1 w2)]

theorem mc_spectralNorm_zero {n1 n2 : ℕ} : spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  simp [spectralNorm]

theorem mc_prod_eq_max_mul_min (n₁ n₂ : ℕ) :
    ((n₁ : ℝ) * (n₂ : ℝ)) = ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
  rcases le_total n₁ n₂ with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]

/-! ## Main theorem -/

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ccent, ccent, hCcent, hccent, Hcent⟩ :=
    quadratic_neumann_middle_index_distinct_centered_contribution_small_with_lambda
  obtain ⟨Cbern, cbern, hCbern, hcbern, Hbern⟩ :=
    scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
  obtain ⟨Cuni, cuni, hCuni, hcuni, Huni⟩ :=
    bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails Cbern cbern
      hCbern hcbern
  obtain ⟨Centry, hCentry, Hentry⟩ :=
    quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim
  obtain ⟨Cfro, hCfro, Hfro⟩ :=
    quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim
  obtain ⟨Cpref, hCpref, Hpref⟩ :=
    quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound
  refine ⟨Ccent + Cpref * Cuni * (2 * (Cfro + Centry)), ccent + cuni, by positivity,
    by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hlam0 : 0 < lam := by linarith
  have hNnonneg : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlamneg_nonneg : (0 : ℝ) ≤ Real.rpow lam (-((3 : ℝ) / 2)) := Real.rpow_nonneg hlam0.le _
  -- the centered event has high probability
  have Hc := Hcent β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  by_cases hN1 : max n₁ n₂ = 1
  · -- degenerate case: a single entry, the contribution vanishes identically
    have h1 : n₁ = 1 := by omega
    have h2 : n₂ = 1 := by omega
    subst h1 h2
    have hzero : ∀ Omega : Finset (Fin 1 × Fin 1),
        spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤
          (Ccent + Cpref * Cuni * (2 * (Cfro + Centry))) * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega
      rw [mc_contribution_zero_of_subsingleton, mc_spectralNorm_zero]
      positivity
    have hmono := bernoulli_event_probability_mono ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))
      (fun Omega => spectralNorm
        (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤ Ccent * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega => spectralNorm
        (quadraticNeumannMiddleIndexDistinctContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤
          (Ccent + Cpref * Cuni * (2 * (Cfro + Centry))) * Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 (fun Omega _ => hzero Omega)
    have hcu := mul_le_mul_of_nonneg_right (show ccent ≤ ccent + cuni by linarith) hNnonneg
    linarith
  · -- main case: `max n₁ n₂ ≥ 2`
    have hN2nat : 2 ≤ max n₁ n₂ := by omega
    -- notation
    set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
    set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
    set nmin : ℝ := ((min n₁ n₂ : ℕ) : ℝ) with hnmin
    set L : ℝ := Real.log N with hL
    have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN2nat
    have hN0 : 0 < N := by linarith
    have hnmin0 : 0 < nmin := by
      rw [hnmin]; exact_mod_cast (lt_min hn₁ hn₂)
    have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hN2
    have hL0 : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
    have hμ0pos : 0 < μ₀ := by linarith
    have hm₀pos : 0 < lam * μ₀ ^ ((4 : ℝ) / 3) * N * (r : ℝ) ^ ((4 : ℝ) / 3) * (β * L) := by
      positivity
    have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hm₀pos hsample
    have hprod : ((n₁ : ℝ) * (n₂ : ℝ)) = N * nmin := mc_prod_eq_max_mul_min n₁ n₂
    have hp' : p = (m : ℝ) / (N * nmin) := by rw [hp, hprod]
    have hppos : 0 < p := by rw [hp']; positivity
    -- Bernstein scales for the kernel-square base matrices
    have hentryScale_nonneg : 0 ≤ Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2) := by positivity
    have hfrobScale_nonneg : 0 ≤ Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2) := by
      positivity
    -- pointwise Bernstein tails at level `β + 2`
    have Hpoint : ∀ w : Fin n₁ × Fin n₂,
        bernoulliEventProb p
          (fun Omega =>
            |(fun (w : Fin n₁ × Fin n₂) (Omega : Finset (Fin n₁ × Fin n₂)) =>
                quadraticMiddleIndexDistinctMeanCoefficient Omega S p w) w Omega| ≤
              Cbern * (Real.sqrt (((β + 2) * L) / p) *
                  (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
                (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2)))) ≥
          1 - cbern * Real.rpow N (-(β + 2)) := by
      intro w
      have := Hbern (β + 2) (by linarith) n₁ n₂ m hn₁ hn₂ hm
        (fun Omega => quadraticMiddleIndexDistinctMeanCoefficient Omega S p w)
        (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w)
        (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2))
        (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2))
        (fun Omega =>
          quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
            Omega S p w)
        (Hentry n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w)
        (Hfro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w)
      exact this
    -- union bound over the indices
    have Hu := Huni β p
      (Real.sqrt (((β + 2) * L) / p) *
          (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
        (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2)))
      hβ hp0 hp1 n₁ n₂ hn₁ hn₂
      (fun (w : Fin n₁ × Fin n₂) (Omega : Finset (Fin n₁ × Fin n₂)) =>
        quadraticMiddleIndexDistinctMeanCoefficient Omega S p w) Hpoint
    -- intersection of the two good events
    have Hinter := bernoulli_event_intersection_probability_from_lower_bounds p ccent cuni
      (Real.rpow N (-β))
      (fun Omega => spectralNorm
        (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
          Ccent * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega => ∀ w : Fin n₁ × Fin n₂,
        |(fun (w : Fin n₁ × Fin n₂) (Omega : Finset (Fin n₁ × Fin n₂)) =>
            quadraticMiddleIndexDistinctMeanCoefficient Omega S p w) w Omega| ≤
          Cuni * (Real.sqrt (((β + 2) * L) / p) *
              (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
            (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2))))
      hp0 hp1 Hc Hu
    -- on the intersection, the full contribution is small
    have hscale := mean_scale_bound Cfro Centry β L lam μ₀ (r : ℝ) N nmin (m : ℝ) p hCfro hCentry
      hβ hL2 hlam hμ₀ hr1 hN0 hnmin0 hsample hp'
    have hunit_pos : 0 < Real.sqrt (β * L) * Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2) := by
      apply mul_pos
      · exact Real.sqrt_pos.mpr (by positivity)
      · exact Real.rpow_pos_of_pos (by positivity) _
    have hscale_pos : 0 < Real.sqrt (((β + 2) * L) / p) *
          (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
        (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2)) := by
      positivity
    have hsub : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        (spectralNorm (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
            Ccent * Real.rpow lam (-((3 : ℝ) / 2)) ∧
          ∀ w : Fin n₁ × Fin n₂,
            |(fun (w : Fin n₁ × Fin n₂) (Omega : Finset (Fin n₁ × Fin n₂)) =>
                quadraticMiddleIndexDistinctMeanCoefficient Omega S p w) w Omega| ≤
              Cuni * (Real.sqrt (((β + 2) * L) / p) *
                  (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
                (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2)))) →
        spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
          (Ccent + Cpref * Cuni * (2 * (Cfro + Centry))) * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega ⟨hcent, huni⟩
      -- abbreviations
      set scale : ℝ := Real.sqrt (((β + 2) * L) / p) *
          (Cfro * μ₀ ^ ((3 : ℝ) / 2) * ((r : ℝ) / nmin) ^ ((3 : ℝ) / 2)) +
        (((β + 2) * L) / p) * (Centry * μ₀ ^ 2 * (((r : ℝ) / nmin) ^ 2)) with hscale_def
      set unit : ℝ := Real.sqrt (β * L) * Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2)
        with hunit_def
      have hCcoef : 0 < Cuni * scale / unit := by positivity
      have heq : Cuni * scale / unit * Real.sqrt (β * L) *
          Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2) = Cuni * scale := by
        rw [hunit_def]
        have h1 : Real.sqrt (β * L) ≠ 0 := by
          rw [hunit_def] at hunit_pos
          exact (Real.sqrt_pos.mpr (by positivity)).ne'
        have h2 : Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2) ≠ 0 :=
          (Real.rpow_pos_of_pos (by positivity) _).ne'
        field_simp
      have hbound : QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p
          (Cuni * scale / unit * Real.sqrt (β * L) *
            Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2)) := by
        rw [heq]
        exact huni
      have hmean := Hpref β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 Omega
        (quadratic_neumann_middle_index_distinct_mean_as_coefficient_sum Omega S p)
        (sign_matrix_frobenius_norm_le_sqrt_rank S) (Cuni * scale / unit) hCcoef hbound
      -- rewrite the mean bound
      have hmean' : spectralNorm (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
          Cpref * Cuni * (2 * (Cfro + Centry)) * Real.rpow lam (-((3 : ℝ) / 2)) := by
        have e1 : Cpref * (Cuni * scale / unit) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) *
            Real.sqrt (β * L) * Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2)
            = Cpref * (Cuni * scale / unit * Real.sqrt (β * L) *
                Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2)) *
              (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) := by ring
        have e2 : Cpref * (Cuni * scale) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ)
            = (Cpref * Cuni * (scale * p⁻¹ * Real.sqrt (r : ℝ))) * (1 - p) := by ring
        have h1p : 1 - p ≤ 1 := by linarith
        have hbase : 0 ≤ Cpref * Cuni * (scale * p⁻¹ * Real.sqrt (r : ℝ)) := by positivity
        calc spectralNorm (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p)
            ≤ Cpref * (Cuni * scale / unit) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) *
              Real.sqrt (β * L) * Real.rpow (μ₀ * N * (r : ℝ) / (m : ℝ)) ((3 : ℝ) / 2) := hmean
          _ = Cpref * (Cuni * scale) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) := by rw [e1, heq]
          _ = (Cpref * Cuni * (scale * p⁻¹ * Real.sqrt (r : ℝ))) * (1 - p) := e2
          _ ≤ (Cpref * Cuni * (scale * p⁻¹ * Real.sqrt (r : ℝ))) * 1 :=
              mul_le_mul_of_nonneg_left h1p hbase
          _ = Cpref * Cuni * (scale * p⁻¹ * Real.sqrt (r : ℝ)) := by ring
          _ ≤ Cpref * Cuni * (2 * (Cfro + Centry) * lam ^ (-((3 : ℝ) / 2))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact hscale
          _ = Cpref * Cuni * (2 * (Cfro + Centry)) * Real.rpow lam (-((3 : ℝ) / 2)) := by
              rw [Real.rpow_eq_pow]; ring
      exact quadratic_neumann_middle_index_distinct_bound_from_centered_and_mean_bounds S Omega p
        Ccent (Cpref * Cuni * (2 * (Cfro + Centry))) lam hcent hmean'
    have hmono := bernoulli_event_probability_mono p _ _ hp0 hp1 hsub
    linarith
