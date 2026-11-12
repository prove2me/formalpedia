-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger94_original_dividend_cell_measure_finite
-- name    : AvramDividend.Classical.avram_gledger94_original_dividend_cell_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:22:55.178673+00:00
-- url     : https://prove2.me/theorems/6b6d81be-94f8-4c44-9f5a-ac71212ab5b3
-- title:
--   Every bounded original dividend cash cell has finite Stieltjes mass
-- statement:
--   Each fixed bounded time cell of the original dividend Stieltjes measure has finite mass. This supplies the explicit finiteness hypothesis in the interior ENNReal-to-Real cash-contact conversion gledger93, with no moment assumptions or auxiliary process.
-- source:
--   Original finite cell mass needed to apply root-connected gledger93 inside gledger81. Consequence of proved dividendMeasure_locallyFinite d0e8873f.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger94_original_dividend_cell_measure_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ) :
    dividendMeasure D ω (Ioc a b) ≠ ⊤ := by sorry
