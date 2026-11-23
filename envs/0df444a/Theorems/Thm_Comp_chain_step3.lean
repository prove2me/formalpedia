-- Prove2me | Theorems.Thm_Comp_chain_step3
-- name    : Comp.chain_step3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:57:45.025354+00:00
-- url     : https://prove2.me/theorems/45130055-61bf-4cb9-9742-a7ffaed20eac
-- title:
--   Comp: chain step3
-- statement:
--   The Comp construction uses the chain step3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L290-L291
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L290-L291

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_step3 : chainGame.gStepF chainSafe chainR2 = chainR3 := by sorry
