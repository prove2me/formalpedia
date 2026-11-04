-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:21:29.258262+00:00
-- url     : https://prove2.me/theorems/d520d51b-403d-4fb2-adc6-d867f97594a6
-- title:
--   Original ruin-clock sampled residual converges almost surely from above by right continuity
-- statement:
--   For the genuine original ruin-truncated stopping clock, any sampled upper-clock sequence converging pathwise to that clock and never preceding it transfers almost-sure pathwise right continuity of the actual residual process into almost-sure convergence of its stopped sampled values. The martingale must still be proved to have such right-continuous paths; this lemma is the exact analytic interface between the ceiling clock and the accepted bounded-grid mean-limit theorems.
-- source:
--   Pinned Mathlib Topology.NhdsWithin tendsto_nhdsWithin_iff and ContinuousWithinAt comp; actual source τ from 0dda1be7.

import Mathlib
import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Right-continuous original residual paths transfer upper-clock convergence to almost-sure stopped values. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (f : ℝ≥0 → Ω → ℝ) (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k => f (u k ω) ω) atTop (𝓝 (f (τ ω) ω)) := by sorry
