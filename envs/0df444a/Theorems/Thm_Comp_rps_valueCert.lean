-- Prove2me | Theorems.Thm_Comp_rps_valueCert
-- name    : Comp.rps_valueCert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:19:34.63279+00:00
-- url     : https://prove2.me/theorems/0ef6a664-6d16-44da-a4c2-b25a4ba6c846
-- title:
--   Comp: rps value Cert
-- statement:
--   The certificate: uniform play holds the row player's loss to `0` against every pure column and
--       guarantees the column player `0` against every pure row. Closed by `decide`, which is the whole
--       point of the exercise -- finitely many exact rational comparisons, no recursion, nothing about
--       how the witnesses were found.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L99-L106
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L99-L106

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.rps_valueCert : rpsMatrixQ.ValueCert 0 rpsUnif rpsUnif := by sorry
