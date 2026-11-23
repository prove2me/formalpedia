-- Prove2me | Theorems.Thm_Comp_mp_valueCert
-- name    : Comp.mp_valueCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:20:59.879074+00:00
-- url     : https://prove2.me/theorems/f3c68106-d8ed-4367-a786-4857dec61565
-- title:
--   Comp: mp value Cert
-- statement:
--   The certificate for matching pennies.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L138-L145
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L138-L145

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.mp_valueCert : mpMatrixQ.ValueCert 0 mpUnif mpUnif := by sorry
