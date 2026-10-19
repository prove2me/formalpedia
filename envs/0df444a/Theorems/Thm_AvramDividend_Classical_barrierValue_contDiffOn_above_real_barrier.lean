-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_contDiffOn_above_real_barrier
-- name    : AvramDividend.Classical.barrierValue_contDiffOn_above_real_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:04:38.143636+00:00
-- url     : https://prove2.me/theorems/62a5a50c-1f87-4288-bf27-fe7b765d7a02
-- title:
--   The dividend barrier value is twice continuously differentiable on its strict affine region
-- statement:
--   For an arbitrary real-valued function W and any finite nonnegative real barrier a, the formal barrierValue W a is C2 on the open half-line (a,+infinity). No assumptions about W's derivative or scale-function harmonicity are required since the formal barrier candidate is exactly affine there. The result separates the easy right-hand C2 part of Gaussian positive-barrier gluing from the genuinely hard left-hand scale regularity and matching jets at a.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierValue_contDiffOn_above_real_barrier (W : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ContDiffOn ℝ 2 (barrierValue W a) (Ioi a) := by sorry
