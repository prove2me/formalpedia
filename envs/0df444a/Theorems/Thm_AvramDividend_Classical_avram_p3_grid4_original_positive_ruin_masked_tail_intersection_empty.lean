-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_ruin_masked_tail_intersection_empty
-- name    : AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_masked_tail_intersection_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:04:23.767395+00:00
-- url     : https://prove2.me/theorems/3bb207cb-852b-4ab8-a57c-f4e9384301c9
-- title:
--   Shrinking actual pre-ruin payment-mask tails have empty common intersection
-- statement:
--   For actual original X,D and a positive finite ruin endpoint tau, any real lower-tail displacement delta_n tending to zero gives an empty intersection of the paymentTimes-filtered half-open tails (tau-delta_n,tau]. Points strictly below tau are eventually excluded; the endpoint tau is excluded by the exact original paymentTimes ruin convention. This is the set-limit ingredient for continuity from above of the integrable original discounted contact-cell cash.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_masked_tail_intersection_empty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (⋂ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ : ℝ) - δ n) (τ : ℝ)) = ∅ := by sorry
