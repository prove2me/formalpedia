-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_BV_generator_borel_gridfree
-- name    : AvramDividend.Classical.avram_bv_meas7_original_BV_generator_borel_gridfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:59.869497+00:00
-- url     : https://prove2.me/theorems/5263789b-7316-4d80-a404-034f5fb09336
-- title:
--   Original bounded-variation generator is Borel without any physical-grid hypothesis
-- statement:
--   For the original spectrally negative Levy process X with bounded variation, a Borel real test function w has a Borel original Levy generator X.generator w. This removes unrelated uniform physical-grid assumptions from a previously Proved source theorem and supplies the generator-measurability factor for arbitrary deterministic stopped BV grids.
-- source:
--   Source-faithful extraction of the accepted full proof of avram_a19_generator_borel (05d7ca17-7289-42a4-83d2-add9c45f4686): its proof uses only hBV, Measurable w, measurable_deriv, original X.nu sigma-finiteness and a measurable parameter integral, and does not mention T, u, hgrid, hmono or huniform. This child will be used to prove AEStronglyMeasurable of the generator component of the original B sum on arbitrary deterministic grids in open 4f851376. No equality-in-law or full-kernel L1 claim.

import Mathlib
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_BV_generator_borel_gridfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable (fun y : ℝ => X.generator w y) := by sorry
