-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_compensator_integral_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_compensator_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:42:20.17659+00:00
-- url     : https://prove2.me/theorems/6e165d6a-1b75-46bc-a1d4-e6373b64bdc8
-- title:
--   Exact positive compensated Levy generator integral equals strict ruin overshoot for all caps
-- statement:
--   For the genuine compensated source Levy generator at every strict upper reserve and every optimal cap including zero, the integral of the positive jump kernel over all negative jumps equals exactly the finite-band strict ruin-crossing overshoot integral. Integrability follows independently from the source Levy measure itself. This handles the crossing and landing boundary explicitly.
-- source:
--   All-cap compensated positive jump kernel identity and source Levy finite-away-from-zero integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_compensator_integral_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : (∫ y in Iio (0 : ℝ), max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ∂X.ν) = ∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν := by sorry
