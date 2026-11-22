-- Prove2me | Theorems.Thm_Csg_pointRow_mem
-- name    : Csg.pointRow_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:36.673246+00:00
-- url     : https://prove2.me/theorems/a7a27538-cff4-4637-a9e2-4a16c154dd7d
-- title:
--   Csg: point Row mem
-- statement:
--   The Csg construction uses the point Row mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L247-L249
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L247-L249

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.pointRow_mem (m : RowMove) : pointRow m ∈ stdSimplex ℝ RowMove := by sorry
