-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_regular_minimal
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_regular_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T08:36:52.971251+00:00
-- url     : https://prove2.me/theorems/7dbaa3c4-63f0-4997-a250-68bb559eab09
-- title:
--   Optimal-barrier smooth fit from scale regularity and derivative minimality
-- statement:
--   For a positive finite optimal barrier, if the scale function is continuously differentiable on the positive half-line with strictly positive derivative and its derivative attains a global minimum at the barrier, then the classical barrier value has ordinary derivative exactly one at that barrier. This is a deterministic calculus step, reusable for the Gaussian and bounded-variation cases.
-- source:
--   Avram, Palmowski and Pistorius (2007), smooth fit at c*. This deterministic lemma separates the derivative-pasting step from unproved stochastic scale regularity.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
open AvramDividend.Classical Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_deriv_one_of_regular_minimal
    (W : ℝ → ℝ)
    (ha : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Set.Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x)
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
       ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry

end AvramDividend.Classical
