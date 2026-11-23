-- Prove2me | Theorems.Thm_Comp_chain_step2
-- name    : Comp.chain_step2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:57:51.106302+00:00
-- url     : https://prove2.me/theorems/1968d826-eb25-4f94-bcbf-f03cff54c6e1
-- title:
--   Comp: chain step2
-- statement:
--   The Comp construction uses the chain step2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L287-L288
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L287-L288

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_step2 : chainGame.gStepF chainSafe chainSafe = chainR2 := by sorry
