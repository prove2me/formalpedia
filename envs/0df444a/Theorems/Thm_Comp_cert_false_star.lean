-- Prove2me | Theorems.Thm_Comp_cert_false_star
-- name    : Comp.cert_false_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:54:22.666796+00:00
-- url     : https://prove2.me/theorems/e8f55501-3032-4a20-bbeb-894151ae36c7
-- title:
--   Comp: cert false star
-- statement:
--   The absorbing state's stage game at `vStar` has value `vStar false`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L170-L180
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L170-L180

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.cert_false_star :
    (twoGame.shapleyGameQ false vStar).ValueCert (vStar false) pure2 pure2 := by sorry
