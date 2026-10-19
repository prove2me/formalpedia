-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_contDiffOn_two_above_real_cstar
-- name    : AvramDividend.Classical.vcstar_contDiffOn_two_above_real_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:26:01.233671+00:00
-- url     : https://prove2.me/theorems/efd127ca-fa32-4bf4-ad2b-6a141f924dc4
-- title:
--   The exact optimal barrier candidate is C2 strictly above cstar
-- statement:
--   The pinned formal optimal barrier candidate vcstar W, for any function W, is twice continuously differentiable at every real reserve strictly greater than (cstar W).toReal. This uses the exact definitional equality to barrierValue W a and the proved C2 result for its affine strict-right branch, with the nonnegativity of the ENNReal-to-real cap. It asserts nothing at the barrier or about the smoothness of W on the left.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_contDiffOn_above_real_barrier

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_contDiffOn_two_above_real_cstar (W : ℝ → ℝ) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (cstar W).toReal) := by sorry
