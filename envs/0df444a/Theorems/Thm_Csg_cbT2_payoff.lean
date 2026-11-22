-- Prove2me | Theorems.Thm_Csg_cbT2_payoff
-- name    : Csg.cbT2_payoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:15:45.876531+00:00
-- url     : https://prove2.me/theorems/9b6ee53b-d520-49db-b46b-0e5e5a41aaaf
-- title:
--   Csg: cb T2 payoff
-- statement:
--   The payoff at `t2`, for an arbitrary row strategy `p` and any column strategy `q` in the
--       simplex -- the column player has no influence at all.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L321-L333
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L321-L333

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbT2_payoff (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hq : q ∈ stdSimplex ℝ ColMove) :
    (cbCSG.stageGame .t2 v).payoff p q = p .b * v .t2 + p .d * ((v .t1 + v .t3) / 2) := by sorry
