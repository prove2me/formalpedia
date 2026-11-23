-- Prove2me | Theorems.Thm_Comp_chain_step1
-- name    : Comp.chain_step1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:57:16.907008+00:00
-- url     : https://prove2.me/theorems/7f955542-0bae-443b-827b-78d70a4051b9
-- title:
--   Comp: chain step1
-- statement:
--   The Comp construction uses the chain step1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L284-L285
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L284-L285

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_step1 : chainGame.gStepF chainSafe Finset.univ = chainSafe := by sorry
