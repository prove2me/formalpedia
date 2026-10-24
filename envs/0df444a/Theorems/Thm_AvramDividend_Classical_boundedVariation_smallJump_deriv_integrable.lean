-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable
-- name    : AvramDividend.Classical.boundedVariation_smallJump_deriv_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:55:43.369279+00:00
-- url     : https://prove2.me/theorems/eb782816-b4b8-40bd-bd18-7a8a313c010b
-- title:
--   The bounded-variation generator's derivative-weighted small-jump term is integrable
-- statement:
--   The bounded-variation Lévy first-moment hypothesis implies integrability of the derivative-weighted compensation term deriv w x * y on (-1,0), allowing the first derivative to be extracted from the small-jump generator integral.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_smallJump_deriv_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (fun y : ℝ => deriv w x * y) (Ioo (-1 : ℝ) 0) X.ν := by sorry
