-- Prove2me | Theorems.Thm_Comp_chain_fixed
-- name    : Comp.chain_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:58:37.704488+00:00
-- url     : https://prove2.me/theorems/aa1f9f88-c9bb-45cd-adee-9cd3c9581e14
-- title:
--   Comp: chain fixed
-- statement:
--   The stabilisation: `chainGood` is a fixed point of the step. This is the hypothesis that
--       supplies the *lower* half of the identification for free, a greatest fixed point being above
--       every post-fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L299-L300
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L299-L300

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_fixed : chainGame.gStepF chainSafe chainGood = chainGood := by sorry
