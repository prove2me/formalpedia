-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_upper_clock_rightcont_uniform_L2_mean_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_uniform_L2_mean_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:42:13.023024+00:00
-- url     : https://prove2.me/theorems/950d8fb9-2636-47be-b15f-923a9913c379
-- title:
--   Exact original stopped ruin-clock residual is genuinely L1 centred from varying upper-clock uniform positive/negative L2
-- statement:
--   For the exact original ruin-truncated clock and upper mesh sampling, a.e. right continuity of the same residual path gives a.e. convergence of its positive and negative parts. Uniform finite second-moment estimates for both parts and genuine centred finite-stage signed expectations then imply the exact stopped residual is Integrable and has mean zero. This is an alternative to a single dominating envelope, permitting source Gaussian/small-jump L2 closure while retaining separate large-jump L1 obligations.
-- source:
--   Proved P4-E original right-continuity upper-clock convergence and source signed two-sided uniform L2 mean-limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine two-sided L2 estimates and right-continuous original clock limits give a centred L1 residual. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_uniform_L2_mean_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω))
    (hPosMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (f (u k ω) ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (-(f (u k ω) ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable
      (fun ω => max (f (τ ω) ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable
      (fun ω => max (-(f (τ ω) ω)) 0) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable
      (fun ω => (max (f (u k ω) ω) 0) ^ 2) P ∧
      (∫ ω, (max (f (u k ω) ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable
      (fun ω => (max (-(f (u k ω) ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(f (u k ω) ω)) 0) ^ 2 ∂P) ≤ C)
    (hSplit : ∀ k,
      (∫ ω, max (f (u k ω) ω) 0 ∂P) -
      (∫ ω, max (-(f (u k ω) ω)) 0 ∂P) = 0) :
    Integrable (fun ω => f (τ ω) ω) P ∧
      (∫ ω, f (τ ω) ω ∂P) = 0 := by sorry
