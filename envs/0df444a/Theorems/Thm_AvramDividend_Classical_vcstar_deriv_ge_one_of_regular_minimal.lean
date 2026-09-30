-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
-- name    : AvramDividend.Classical.vcstar_deriv_ge_one_of_regular_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:43:06.223873+00:00
-- url     : https://prove2.me/theorems/ab68511d-f20e-4a60-b3ab-5788eae1aef5
-- title:
--   Piecewise calculus: C1 regularity and minimal derivative imply vcstar' >= 1
-- statement:
--   Let W be C1 on (0,∞), with positive derivative there. If the real barrier level c* is zero or, when positive, is a global minimiser of W', then the piecewise barrier value vc* is differentiable at every x>0 and has derivative at least one. This is the elementary calculus layer of Lemma 3(i).
-- source:
--   Elementary calculus decomposition of Avram, Palmowski, Pistorius, arXiv:math/0702893v1, Lemma 3(i), after isolating the scale-function regularity, positivity, and c* minimality inputs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_deriv_ge_one_of_regular_minimal (W : ℝ → ℝ)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x)
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧
      1 ≤ deriv (vcstar W) x := by sorry

end AvramDividend.Classical
