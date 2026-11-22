-- Prove2me | Theorems.Thm_Csg_cbStageValue_const
-- name    : Csg.cbStageValue_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:59:16.153677+00:00
-- url     : https://prove2.me/theorems/9506b524-e095-4477-afe2-942a5d081bab
-- title:
--   Csg: cb Stage Value const
-- statement:
--   At a state where every joint action gives the same payoff `c`, the stage value is `c` --
--       every strategy pair is trivially a saddle point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L259-L289
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L259-L289

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbStageValue_const (v : CBState → ℝ) (s : CBState) (c : ℝ)
    (hc : ∀ (i : RowMove) (j : ColMove), (cbCSG.stageGame s v).A i j = c) :
    cbCSG.stageValue s v = c := by sorry
