-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_complete_root_at_zero
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_complete_root_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:15:55.950129+00:00
-- url     : https://prove2.me/theorems/6f740c45-2411-4aae-a1ad-7e2b67d798b6
-- title:
--   Both original optimality assertions at zero capital in unbounded variation
-- statement:
--   Closes both conjunctions of the original barrier-optimality root at zero initial reserve in the unbounded-variation case. Original barrier admissibility and discounted reward are supplied by the proved attainment theorem; the exact capped and unrestricted values follow from proved original instant-ruin and W(0)=0 results. There are no extra regularity, generator, stopped-martingale or positive-reserve hypotheses.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_full_root_value

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_complete_root_at_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    IsAdmissibleLe X 0 (cstar W) (barrierStrategy X 0 (cstar W).toReal) ∧
    dividendValue X q 0 (barrierStrategy X 0 (cstar W).toReal) =
      ENNReal.ofReal (vcstar W 0) ∧
    valueFunctionLe X q (cstar W) 0 = ENNReal.ofReal (vcstar W 0) ∧
    IsAdmissible X 0 (barrierStrategy X 0 (cstar W).toReal) ∧
    valueFunction X q 0 = ENNReal.ofReal (vcstar W 0) := by sorry
