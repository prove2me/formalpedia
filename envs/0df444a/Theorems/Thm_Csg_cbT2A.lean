-- Prove2me | Theorems.Thm_Csg_cbT2A
-- name    : Csg.cbT2A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:15:31.401438+00:00
-- url     : https://prove2.me/theorems/1b96b7ae-b4e5-403a-872d-718bd063624d
-- title:
--   Csg: cb T2 A
-- statement:
--   The row player's own certain payoff at `t2`, playing `i` against *any* column action -- `v .t2`
--       for `b`, the average `(v .t1 + v .t3) / 2` for `d`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L311-L317
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L311-L317

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbT2A (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t2 v).A i j = if i = .b then v .t2 else (v .t1 + v .t3) / 2 := by sorry
