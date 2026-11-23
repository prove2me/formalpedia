-- Prove2me | Theorems.Thm_Comp_supportF_dirac
-- name    : Comp.supportF_dirac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:56:44.716484+00:00
-- url     : https://prove2.me/theorems/9208f4bc-f1b2-4e56-ace7-574f19a39f6c
-- title:
--   Comp: support F dirac
-- statement:
--   A point-mass row's support is a singleton.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L205-L208
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L205-L208

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.supportF_dirac {s : Chain} {a1 a2 : Bool} {t : Chain}
    (hK : chainGame.K s a1 a2 = dirac t) : chainGame.supportF s a1 a2 = {t} := by sorry
