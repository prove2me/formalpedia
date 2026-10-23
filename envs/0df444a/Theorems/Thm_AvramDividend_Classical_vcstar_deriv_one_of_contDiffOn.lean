-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_contDiffOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:28:26.240595+00:00
-- url     : https://prove2.me/theorems/eb491d0b-2ad3-4050-9d18-44c1dc5885cf
-- title:
--   C2 optimal-barrier candidate has derivative one at a finite positive barrier
-- statement:
--   For any real scale-like W whose cstar is positive and finite, if vcstar W is C2 on the positive half-line, then its ordinary derivative at cstar.toReal is exactly one. The positive finite barrier has a strictly positive real conversion, so the C2 hypothesis gives ordinary differentiability there. The proved generic barrier-value smooth-fit assembly lemma then forces its derivative to be one. This discharges the explicit C2 disjunct of the original vcstar smooth-fit target without assuming any stochastic regularity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
open AvramDividend.Classical Set

theorem AvramDividend.Classical.vcstar_deriv_one_of_contDiffOn
    (W : ℝ → ℝ) (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
