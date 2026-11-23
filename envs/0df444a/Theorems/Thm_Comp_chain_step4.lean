-- Prove2me | Theorems.Thm_Comp_chain_step4
-- name    : Comp.chain_step4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:58:10.035705+00:00
-- url     : https://prove2.me/theorems/2abba5e3-39a1-445f-b1fc-eab0117fa087
-- title:
--   Comp: chain step4
-- statement:
--   The Comp construction uses the chain step4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L293-L294
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L293-L294

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_step4 : chainGame.gStepF chainSafe chainR3 = chainGood := by sorry
