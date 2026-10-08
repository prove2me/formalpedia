-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar
-- name    : AvramDividend.Classical.vcstar_eq_scaledW_on_Iic_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:30:31.678986+00:00
-- url     : https://prove2.me/theorems/29a56575-11dd-4505-92f8-857cd713f5e9
-- title:
--   Optimal barrier candidate agrees with the scaled scale-function branch on all reserves at or below c-star
-- statement:
--   The formal barrier value candidate vcstar W equals its scale-function branch u(z)=W(z)/W'(c*) at every reserve z≤c*, including negative z. On [0,c*] this follows directly from the middle branch of barrierValue; on negative reserves both expressions vanish because W(z)=0 and divE handles the possibly infinite denominator. This equality is the entire below-boundary function-agreement premise of generator locality at c*, and does not require any stochastic regularity or c* positivity assumption. Source-neutral piecewise bridge used by the matched weighted-jet proof.
-- source:
--   Direct formal equivalence of the piecewise barrierValue and q-scale extension-by-zero formulas (5.1) in Avram, Palmowski, Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_eq_scaledW_on_Iic_cstar
    (W : ℝ → ℝ) (hnegative : ∀ z : ℝ, z < 0 → W z = 0)
    (z : ℝ) (hz : z ≤ (cstar W).toReal) :
    vcstar W z =
      divE (W z) (scaleDeriv W (cstar W).toReal) := by
  sorry
end AvramDividend.Classical
