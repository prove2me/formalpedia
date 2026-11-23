-- Prove2me | Theorems.Thm_Csg_cbInnerGfp_eq
-- name    : Csg.cbInnerGfp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:16:14.749046+00:00
-- url     : https://prove2.me/theorems/59172197-c185-46af-b403-94b790fff047
-- title:
--   Csg: cb Inner Gfp eq
-- statement:
--   The Csg construction uses the cb Inner Gfp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L518-L600
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L518-L600

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbInnerGfp_eq (b : CBState → Set.Icc (0 : ℝ) 1) :
    (cbCSG.coBuchiInnerOp cbU cbR_zero b).gfp = cbGClosed b := by sorry
