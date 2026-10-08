-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_magnitude_exponential_integrable
-- name    : AvramDividend.Classical.bv_positive_magnitude_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:20:41.008678+00:00
-- url     : https://prove2.me/theorems/7d5f65bc-9559-4925-8efc-60bbd329819c
-- title:
--   The bounded-variation positive jump-magnitude exponential compensator is integrable
-- statement:
--   For a bounded-variation spectrally negative Lévy process and θ≥1, the positive jump-magnitude function z↦1-exp(-θz) is integrable under the pushforward of the Lévy measure by y↦max(-y,0). On negative jumps the pullback is 1-exp(θy), the negative of the already-proved integrable function exp(θy)-1; outside the negative half-line the pullback vanishes because max(-y,0)=0. Integrability is then transferred through the measurable pushforward.
-- source:
--   Proved bv_exponential_jump_integrable UUID e61e3f45-d1c6-49d7-9d06-a9433505b01d; canonical jump-magnitude map; pinned Mathlib integrable_map_measure and IntegrableOn.integrable_indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_positive_magnitude_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-θ * (z : ℝ)))
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
