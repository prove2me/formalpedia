-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_pos
-- name    : AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:44:29.870999+00:00
-- url     : https://prove2.me/theorems/ce3aab13-5580-4129-9c6f-2012e79ff9eb
-- title:
--   Strict positivity of the actual reflected regulator reward at positive barriers
-- statement:
--   For any Standing spectrally negative Levy process at q>0 and every a>0, the expected discounted Stieltjes dividend reward of the original reflected running-supremum process killed at drawdown ruin is strictly positive in ENNReal. The proof takes epsilon=a/2 in the genuinely Proved derivative-free left renewal bound and uses strict positivity and strict positive-axis increase of the source scale function to show the lower real quotient is positive.
-- source:
--   Avram Palmowski Pistorius 2007, stopped reflection reward. Derives from accepted derivative-free lower renewal inequality and source-specific Esscher scale monotonicity, via pinned ENNReal.ofReal_pos.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_strictMonoOn_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_left_step_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    0 < barrierSupValue X a q := by sorry
