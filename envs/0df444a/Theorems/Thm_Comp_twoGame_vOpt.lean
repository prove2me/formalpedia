-- Prove2me | Theorems.Thm_Comp_twoGame_vOpt
-- name    : Comp.twoGame_vOpt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:39:24.885766+00:00
-- url     : https://prove2.me/theorems/c5f2825b-37a3-49c8-86ab-38ddf1e55266
-- title:
--   Comp: two Game v Opt
-- statement:
--   **The exact value of this concurrent game**, as a statement about the real-valued `vOpt` of
--       `Csg/DiscountedValueIteration.lean`: `(2/3, 2)`, with no error term. The Shapley operator is a
--       contraction, so its fixed point is unique, and exhibiting one rational fixed point therefore
--       identifies `vOpt` outright.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L194-L196
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L194-L196

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.twoGame_vOpt :
    (fun s => ((vStar s : ℚ) : ℝ)) = (twoGame.toDiscountedCSG twoGame_wf).vOpt := by sorry
