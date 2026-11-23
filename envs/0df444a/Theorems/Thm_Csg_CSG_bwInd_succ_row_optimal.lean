-- Prove2me | Theorems.Thm_Csg_CSG_bwInd_succ_row_optimal
-- name    : Csg.CSG.bwInd_succ_row_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:54.838817+00:00
-- url     : https://prove2.me/theorems/dd193f4c-3c5b-4109-9ad9-83d3f2079ece
-- title:
--   CSG: bw Ind succ row optimal
-- statement:
--   **The payoff.** Backward induction actually computes the stage game's value, not just a
--       recursion that happens to type-check: with `n + 1` steps remaining, the row player cannot
--       lower the value below `bwInd rFin (n + 1) s` by unilaterally deviating from the stage game's
--       optimal row strategy while the column player holds its optimal strategy fixed. A direct
--       instantiation of `MatrixGame.value_row_optimal` at `C.stageGame s (C.bwInd rFin n)`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L74-L79
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L74-L79

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.bwInd_succ_row_optimal (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ p' ∈ stdSimplex ℝ A1,
      C.bwInd rFin (n + 1) s ≤ (C.stageGame s (C.bwInd rFin n)).payoff p'
        (C.stageGame s (C.bwInd rFin n)).optimalCol := by sorry
