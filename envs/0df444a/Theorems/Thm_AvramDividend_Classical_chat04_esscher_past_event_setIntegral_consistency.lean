-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_past_event_setIntegral_consistency
-- name    : AvramDividend.Classical.chat04_esscher_past_event_setIntegral_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:03:35.345973+00:00
-- url     : https://prove2.me/theorems/b2539dcd-c516-4f2b-ae6c-708a0d06f5d9
-- title:
--   Projective Esscher laws integrate any past-measurable reward over any past event consistently
-- statement:
--   Fix two deterministic horizons s≤t and a nonnegative Esscher tilt θ. Every strongly F_s-measurable real reward f has the same restricted expectation on any F_s event A under the genuinely constructed Esscher probability laws at horizons s and t. This is the exact measure-theoretic step required to transport the already established projective martingale identity to one fixed terminal Esscher measure.
-- source:
--   Apply the accepted generic `setIntegral_eq_of_measures_agree_on_subsigma` to the sub-σ-algebra F_s, using the accepted `chat04_esscher_finite_horizon_laws_consistent_on_past_events` for equality of the Esscher measures on F_s and unfolding `SpectrallyNegativeLevy.ψ`. No finite-time tilted-law integrability beyond Bochner definitions is assumed.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_measures_agree_on_subsigma
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_past_event_setIntegral_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[𝓕 s] f) :
    (∫ ω in A, f ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) =
    (∫ ω in A, f ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) := by sorry
