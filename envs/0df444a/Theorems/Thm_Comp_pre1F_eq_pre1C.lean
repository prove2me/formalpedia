-- Prove2me | Theorems.Thm_Comp_pre1F_eq_pre1C
-- name    : Comp.pre1F_eq_pre1C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:57:16.270805+00:00
-- url     : https://prove2.me/theorems/041654c9-bf7c-43a1-b4f0-40f7a500fe62
-- title:
--   Comp: pre1 F eq pre1 C
-- statement:
--   The game's `pre1F` is `pre1C`: `supportF_eq_chainSupp` rewritten inside the filter.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L236-L239
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L236-L239

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.pre1F_eq_pre1C (x : Finset Chain) : chainGame.pre1F x = pre1C x := by sorry
