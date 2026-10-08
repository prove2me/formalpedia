-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_contDiffOn_Ioo_of_scaleFunction
-- name    : AvramDividend.Classical.barrierValue_contDiffOn_Ioo_of_scaleFunction
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:11:09.291242+00:00
-- url     : https://prove2.me/theorems/65142bce-7b97-475c-a252-af8b8ccfbb86
-- title:
--   Smoothness of a positive-barrier value below the barrier from scale-function smoothness
-- statement:
--   At every reserve strictly between zero and a positive barrier a, barrierValue W a is the scale function W multiplied by the fixed positive constant 1/W'(a). Therefore any C^n regularity of W on (0,a) transfers directly to the barrier-value function on the same interval.
-- source:
--   Elementary source-neutral calculus for equation (5.1) of Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_contDiffOn_Ioo_of_scaleFunction
    (W : ℝ → ℝ) (a : ℝ) (n : ℕ) (ha : 0 < a)
    (hder : 0 < deriv W a)
    (hWdiff : ContDiffOn ℝ n W (Ioo 0 a)) :
    ContDiffOn ℝ n (barrierValue W a) (Ioo 0 a) := by
  sorry

end AvramDividend.Classical
