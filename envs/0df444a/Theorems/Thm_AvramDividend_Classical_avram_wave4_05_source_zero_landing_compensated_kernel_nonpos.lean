-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_zero_landing_compensated_kernel_nonpos
-- name    : AvramDividend.Classical.avram_wave4_05_source_zero_landing_compensated_kernel_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:40:41.38304+00:00
-- url     : https://prove2.me/theorems/89832e5f-26e9-4a46-af4e-4035d89de860
-- title:
--   True source compensated negative jump kernel is nonpositive at exact landing reserve zero
-- statement:
--   Above the optimal barrier the original compensated source jump kernel cannot contribute positively for a jump exactly landing at reserve zero, for zero or positive cap and with any Levy atom at that jump magnitude. The proof uses strict interval endpoints, not a false identification of landing at zero with negative reserve.
-- source:
--   Accepted original source signed compensated kernel bound; strict inequality y<-x excludes the landing atom from ruin strips.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_zero_landing_compensated_kernel_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x (-x) ≤ 0 := by sorry
