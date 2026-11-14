-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB259_original_future_increment_indepFun_prepayment_centre
-- name    : AvramDividend.Classical.avram_gbB259_original_future_increment_indepFun_prepayment_centre
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T20:49:33.874741+00:00
-- url     : https://prove2.me/theorems/ab1d29d2-899f-4815-9634-cec5d1043d21
-- title:
--   Original future Levy increment is function-independent of past-adapted dividend reserve centre
-- statement:
--   Given the original Levy process and its dividend strategy adapted to the original filtration, the past-measurable centre b-x-X(s)+D(s) is function-independent of the future source increment X(t)-X(s). This converts the source-faithful B258 sigma-algebra independence into the exact IndepFun hypothesis used by the uniform Gaussian random interval probability bound B256.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB259_original_future_increment_indepFun_prepayment_centre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (x b : ℝ) :
    IndepFun
      (fun ω => b - x - X.X s ω + D s ω)
      (fun ω => X.X t ω - X.X s ω) P := by sorry
