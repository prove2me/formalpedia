-- Prove2me | Theorems.Thm_Csg_CSG_bwInd_succ_col_optimal
-- name    : Csg.CSG.bwInd_succ_col_optimal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:24:56.825825+00:00
-- url     : https://prove2.me/theorems/ead3929d-603c-40d2-93c4-ac4de63cd5be
-- title:
--   CSG: bw Ind succ col optimal
-- statement:
--   Symmetric counterpart of `bwInd_succ_row_optimal`: the column player cannot raise the value
--       above `bwInd rFin (n + 1) s` by unilaterally deviating from the stage game's optimal column
--       strategy while the row player holds its optimal strategy fixed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L84-L89
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L84-L89

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.bwInd_succ_col_optimal (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ q' ∈ stdSimplex ℝ A2,
      (C.stageGame s (C.bwInd rFin n)).payoff
        (C.stageGame s (C.bwInd rFin n)).optimalRow q' ≤ C.bwInd rFin (n + 1) s := by sorry
