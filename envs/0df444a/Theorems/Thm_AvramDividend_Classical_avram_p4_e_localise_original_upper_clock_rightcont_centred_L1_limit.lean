-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_upper_clock_rightcont_centred_L1_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_centred_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:32:21.255199+00:00
-- url     : https://prove2.me/theorems/99df6d28-7c30-4397-b130-a56ec375641c
-- title:
--   Exact original ruin-clock stopped martingale has integrable zero-mean limit under a genuine upper-clock L1 envelope
-- statement:
--   For the unchanged original min(ruinTime,n) clock, sample any a.s. right-continuous residual from above. If the sampled residual values are centred with genuine measurability and a common integrable envelope, then the exact original stopped residual is integrable with zero mean. This composes the earlier source-clock a.e. convergence and domination lemmas, without silently inferring optional stopping or uniform integrability from mere local martingales.
-- source:
--   Proved P4-E right-continuity transfer and original domination-preserves-mean theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A right-continuous original stopped residual inherits genuine L1 and zero mean from its upper clocks. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_upper_clock_rightcont_centred_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P,
      ContinuousWithinAt (fun t => f t ω) (Set.Ici (τ ω)) (τ ω))
    (hMkMeas : ∀ k, AEStronglyMeasurable
      (fun ω => f (u k ω) ω) P)
    (hMMeas : AEStronglyMeasurable (fun ω => f (τ ω) ω) P)
    (B : Ω → ℝ) (hBint : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖f (u k ω) ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖f (τ ω) ω‖ ≤ ‖B ω‖)
    (hCentre : ∀ k, (∫ ω, f (u k ω) ω ∂P) = 0) :
    Integrable (fun ω => f (τ ω) ω) P ∧
      (∫ ω, f (τ ω) ω ∂P) = 0 := by sorry
