-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integrable
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:57:53.801298+00:00
-- url     : https://prove2.me/theorems/91c509eb-e9eb-4119-be1b-8bee163cc127
-- title:
--   Genuine source Levy integrability of the strict small-ruin overshoot defect
-- statement:
--   For the actual original spectrally negative Levy process and any strictly positive reserve x, under the genuine second-moment Levy integrability condition, the exact small-ruin overshoot defect y↦max(0,-vcstar(x)-y) restricted to jumps -1<y<-x is Bochner integrable under the source Levy measure. The strict band is separated from zero and has finite measure; the defect is measurable and bounded there by max(0,1-vcstar(x)). The resulting global indicator kernel is integrable without a Levy first-moment requirement. Together with the independently Proved source positive-jump-part identity, this gives the quantitative integrable positive compensated kernel on the true source generator's negative-jump domain.
-- source:
--   Original Avram–Palmowski–Pistorius (2007) Levy generator compensation; Proved negative_jump_truncation_measure_finite and Mathlib IntegrableOn.of_bound under finite measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) : Integrable ((Ioo (-1 : ℝ) (-x)).indicator (fun y : ℝ => max 0 (-vcstar W x - y))) X.ν := by sorry
