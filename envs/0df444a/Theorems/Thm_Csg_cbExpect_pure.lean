-- Prove2me | Theorems.Thm_Csg_cbExpect_pure
-- name    : Csg.cbExpect_pure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:57.843109+00:00
-- url     : https://prove2.me/theorems/83b32062-2741-4de1-b4c7-b5d2aa13538b
-- title:
--   Csg: cb Expect pure
-- statement:
--   The Csg construction uses the cb Expect pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L192-L196
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L192-L196

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbExpect_pure (v : CBState → ℝ) (s t : CBState) (a1 : RowMove) (a2 : ColMove)
    (h : cbK s a1 a2 = PMF.pure t) : cbCSG.expect s a1 a2 v = v t := by sorry
