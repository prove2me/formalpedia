-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_capped_upper_bound_all_capital
-- name    : AvramDividend.Classical.vcstar_capped_upper_bound_all_capital
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:32:59.69471+00:00
-- url     : https://prove2.me/theorems/40dcbaef-9fba-46cd-b671-8a325f221022
-- title:
--   The candidate vcstar bounds the c*-capped value function at every initial surplus
-- statement:
--   Under the hypotheses of Theorem 2 and finiteness of c*, the candidate barrier value vcstar is an upper bound for the value of every dividend strategy whose controlled reserve is capped by c*, for every initial surplus x>=0. This is the comparison half of Theorem 2(i). For x above c* the formal cap forces the excess capital to be paid at time zero, so the proof combines local verification below the cap with the exact above-cap value-function identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 3(i), Proposition 4(i), Lemmas 3-4 and Theorem 2(i), pp.14-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_capped_upper_bound_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
