-- Prove2me | Theorems.Thm_Comp_gStepF_eq
-- name    : Comp.gStepF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:41:22.493862+00:00
-- url     : https://prove2.me/theorems/4253ddb4-62ca-4441-8be5-d351c7edafc1
-- title:
--   Comp: g Step F eq
-- statement:
--   And so the computable sure-safety step is a purely combinatorial one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L242-L245
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L242-L245

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.gStepF_eq (x : Finset Chain) :
    chainGame.gStepF chainSafe x = pre1C x ∩ chainSafe := by sorry
