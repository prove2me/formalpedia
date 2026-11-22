-- Prove2me | Theorems.Thm_Csg_pointCol_mem
-- name    : Csg.pointCol_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:52.8991+00:00
-- url     : https://prove2.me/theorems/5f128e75-98d3-4f0b-a11d-dbb02e130ca8
-- title:
--   Csg: point Col mem
-- statement:
--   The Csg construction uses the point Col mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L251-L253
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L251-L253

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.pointCol_mem (m : ColMove) : pointCol m ∈ stdSimplex ℝ ColMove := by sorry
