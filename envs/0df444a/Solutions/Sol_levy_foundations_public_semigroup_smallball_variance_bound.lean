-- Prove2me | solution 1 for levy_foundations_public_semigroup_smallball_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:24:45.094197+00:00
-- url     : https://prove2.me/submissions/3b39b958-2d4b-4577-b7cf-7b39e16a489d

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_scaled_band_integral_tendsto
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_exists_atomFree_seq_tendsto_zero
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_integrableOn_of_bounded
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball_levy
import Theorems.Thm_levy_foundations_public_gaussian_band_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The small-ball jump variance does not exceed the scaled semigroup
variance; source-backed via atom-free annular approximation. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    ∫ x in {x | |x| < r}, x ^ 2 ∂ν ≤ σ_sq_r := by
  -- Clamp `x²` to `[0, r²]`: globally bounded, continuous, and equal to `x²` on `{|x|<r}`.
  set g : ℝ → ℝ := fun x => min (x ^ 2) (r ^ 2) with hg_def
  have hg_cont : Continuous g := (continuous_pow 2).min continuous_const
  have hr2_nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hg_nn : ∀ x, 0 ≤ g x := fun x => le_min (sq_nonneg x) hr2_nn
  have hg_bnd : ∀ x, |g x| ≤ r ^ 2 := fun x =>
    abs_le.mpr ⟨le_trans (by linarith [hr2_nn]) (hg_nn x), min_le_right _ _⟩
  -- On the ball `{|x| < r}`, the clamp is inactive: `g x = x²`.
  have hg_eq_ball : ∀ x ∈ {x : ℝ | |x| < r}, g x = x ^ 2 := by
    intro x hx
    have hx' : |x| < r := hx
    have : x ^ 2 ≤ r ^ 2 := by
      have := sq_le_sq' (by linarith [abs_lt.mp hx']) (le_of_lt (abs_lt.mp hx').2)
      simpa using this
    exact min_eq_left this
  have h_meas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  -- Atom-free shrinking sequence `δ m ↓ 0` inside `(0, r)`.
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_null, hδ_tendsto⟩ := ProbabilityTheory.IsLevyMeasure.exists_atomFree_seq_tendsto_zero hν hr
  -- Per-`m` ν-band second moment, bounded by `σ_sq_r`.
  have h_band_le : ∀ m, ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν ≤ σ_sq_r := by
    intro m
    -- The band is measurable and contained in the ball.
    have h_meas_band : MeasurableSet {x : ℝ | δ m ≤ |x| ∧ |x| < r} :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const)
    have h_band_sub : {x : ℝ | δ m ≤ |x| ∧ |x| < r} ⊆ {x : ℝ | |x| < r} :=
      fun x hx => hx.2
    -- Step 1: band limit for the clamped `g`, then rewrite to `x²` on both sides.
    have h_band_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν)) := by
      have h := ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_band_integral_tendsto S (hδ := hδ_pos m) (hδρ := hδ_lt m)
        g hg_cont hr2_nn hg_bnd hν (hδ_null m) hν_r h_jump
      -- Swap `g` for `x²` on the band (it lies in the ball where `g = x²`).
      have hswap : ∀ (μ : Measure ℝ),
          ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, g x ∂μ =
            ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂μ :=
        fun μ => setIntegral_congr_fun h_meas_band
          (fun x hx => hg_eq_ball x (h_band_sub hx))
      simpa only [hswap ν, hswap (S.measure (t_seq _) : Measure ℝ)] using h
    -- Step 2: per-`k` comparison band ⊆ ball, using the clamped `g` for integrability.
    have h_compare : ∀ k, (t_seq k).val⁻¹ *
        ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤
        (t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr (t_seq k).2))
      set μ := (S.measure (t_seq k) : Measure ℝ)
      -- Compare via the clamped `g`, which is integrable on the ball (bounded, finite measure).
      have hg_int_ball : IntegrableOn g {x : ℝ | |x| < r} μ :=
        ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded hg_cont
          (fun x => by simpa [Real.norm_eq_abs] using hg_bnd x)
      have h_band : ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂μ =
          ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, g x ∂μ :=
        (setIntegral_congr_fun h_meas_band
          (fun x hx => hg_eq_ball x (h_band_sub hx))).symm
      have h_ball : ∫ x in {x | |x| < r}, x ^ 2 ∂μ =
          ∫ x in {x | |x| < r}, g x ∂μ :=
        (setIntegral_congr_fun h_meas_ball hg_eq_ball).symm
      rw [h_band, h_ball]
      exact setIntegral_mono_set hg_int_ball
        (ae_restrict_of_forall_mem h_meas_ball (fun x _ => hg_nn x))
        (LE.le.eventuallyLE h_band_sub)
    exact le_of_tendsto_of_tendsto' h_band_lim hσ h_compare
  have hquad : IntegrableOn (fun x : ℝ => x ^ 2) {x | |x| < r} ν :=
    ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball_levy hν r
  exact levy_foundations_public_gaussian_band_exhaustion
    ν hν.1 hquad hδ_tendsto h_band_le
