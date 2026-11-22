-- Prove2me | Theorems.Thm_Csg_cbT3_payoff
-- name    : Csg.cbT3_payoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:15:53.418274+00:00
-- url     : https://prove2.me/theorems/e56fe220-0bcf-421f-ae71-02bf441624b7
-- title:
--   Csg: cb T3 payoff
-- statement:
--   The payoff at `t3`, for an arbitrary column strategy `q` and any row strategy `p` in the
--       simplex -- the row player has no influence at all.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L398-L410
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L398-L410

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbT3_payoff (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hp : p ∈ stdSimplex ℝ RowMove) :
    (cbCSG.stageGame .t3 v).payoff p q = q .c * v .t3 + q .d * ((v .t2 + v .t4) / 2) := by sorry
