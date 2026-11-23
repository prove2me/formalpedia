-- Prove2me | Theorems.Thm_Comp_supportF_coin
-- name    : Comp.supportF_coin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:57:00.569891+00:00
-- url     : https://prove2.me/theorems/b902e333-6cc5-4f9b-ba4c-240cc287f656
-- title:
--   Comp: support F coin
-- statement:
--   A coin row's support is the pair.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L211-L214
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L211-L214

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.supportF_coin {s : Chain} {a1 a2 : Bool} {t u : Chain}
    (hK : chainGame.K s a1 a2 = coin t u) : chainGame.supportF s a1 a2 = {t, u} := by sorry
