-- Prove2me | Theorems.Thm_Comp_cert_false_v1
-- name    : Comp.cert_false_v1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:55:59.48942+00:00
-- url     : https://prove2.me/theorems/0e42b030-afeb-49b7-8db3-853ae1d186c2
-- title:
--   Comp: cert false v1
-- statement:
--   The absorbing state's stage game at `v1` has value `v2 false`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L214-L224
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L214-L224

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.cert_false_v1 :
    (twoGame.shapleyGameQ false v1).ValueCert (v2 false) pure2 pure2 := by sorry
