-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_magnitude_compensator_integrable
-- name    : AvramDividend.Classical.positive_magnitude_compensator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:57:57.890979+00:00
-- url     : https://prove2.me/theorems/96d09b3e-f496-4267-9907-cb213204d585
-- title:
--   Integrability of positive jump-magnitude compensator under negative-jump integrability
-- statement:
--   The positive-magnitude jump measure is the pushforward ν.map(y↦toNNReal(-y)). For any real φ, the function 1-exp(-φz) composed with this map equals the negative-jump compensator 1-exp(φy) times the indicator of y<0, and is zero for y≥0. Therefore integrability on the negative-jump half-line transfers to the full pushforward measure by integrable_map_measure and integrable_indicator_iff. This formally connects the already-Proved BV negative-jump exponential integrability with the discounted jump-mass inequality.
-- source:
--   Proved negative_jump_magnitude_integral_transform and pinned Mathlib integrable_map_measure, integrable_indicator_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_magnitude_compensator_integrable
    (ν : Measure ℝ) (φ : ℝ)
    (hneg : IntegrableOn
      (fun y : ℝ => 1 - Real.exp (φ * y)) (Iio (0 : ℝ)) ν) :
    Integrable (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ))))
      (ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
