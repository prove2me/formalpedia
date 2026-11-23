-- Prove2me | Theorems.Thm_Csg_cbT3A
-- name    : Csg.cbT3A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:15:28.629873+00:00
-- url     : https://prove2.me/theorems/fe1fbc35-3e42-4c6a-8bd9-683d1ce94274
-- title:
--   Csg: cb T3 A
-- statement:
--   The column player's own certain payoff at `t3`, playing `j` against *any* row action -- `v .t3`
--       for `c`, the average `(v .t2 + v .t4) / 2` for `d`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L388-L394
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L388-L394

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbT3A (i : RowMove) (j : ColMove) (v : CBState → ℝ) :
    (cbCSG.stageGame .t3 v).A i j = if j = .c then v .t3 else (v .t2 + v .t4) / 2 := by sorry
