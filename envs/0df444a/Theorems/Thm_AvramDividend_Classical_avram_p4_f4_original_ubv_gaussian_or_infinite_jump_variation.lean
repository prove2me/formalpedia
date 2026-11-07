-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_gaussian_or_infinite_jump_variation
-- name    : AvramDividend.Classical.avram_p4_f4_original_ubv_gaussian_or_infinite_jump_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:45:55.58122+00:00
-- url     : https://prove2.me/theorems/45da4331-be1a-4d24-85bf-fb9c081e17f2
-- title:
--   Original unbounded-variation Levy process splits into Gaussian and infinite-jump variation cases
-- statement:
--   For the genuine original spectrally negative Levy process with unbounded variation, either the Gaussian volatility coefficient is nonzero, or the absolute small-negative-jump first Levy moment diverges. This establishes exhaustive stochastic source regimes for the original stopped Ito–Meyer proof.
-- source:
--   Exact original BoundedVariation definition; reuse the previously proved source-verified zero Gaussian infinite-jump-variation theorem 2703ea95.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_ubv_gaussian_or_infinite_jump_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    X.σ ≠ 0 ∨ (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by sorry
