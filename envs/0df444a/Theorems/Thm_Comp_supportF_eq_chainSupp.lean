-- Prove2me | Theorems.Thm_Comp_supportF_eq_chainSupp
-- name    : Comp.supportF_eq_chainSupp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:56:57.480791+00:00
-- url     : https://prove2.me/theorems/2e62b3dd-3daa-4a27-8309-519db7b028b1
-- title:
--   Comp: support F eq chain Supp
-- statement:
--   **The bridge, and the last rational step in the file.** The game's own supports are exactly the
--       table `chainSupp`. Twenty-four cases, each a point mass or a coin by `rfl`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L218-L223
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L218-L223

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.supportF_eq_chainSupp (s : Chain) (a1 a2 : Bool) :
    chainGame.supportF s a1 a2 = chainSupp s a1 a2 := by sorry
