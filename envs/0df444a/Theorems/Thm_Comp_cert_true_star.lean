-- Prove2me | Theorems.Thm_Comp_cert_true_star
-- name    : Comp.cert_true_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:54:17.821512+00:00
-- url     : https://prove2.me/theorems/d2f23c43-d7db-4ca3-a3b9-64428a7302e9
-- title:
--   Comp: cert true star
-- statement:
--   The live state's stage game at `vStar` has value `vStar true`, certified by uniform play.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L157-L167
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L157-L167

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.cert_true_star :
    (twoGame.shapleyGameQ true vStar).ValueCert (vStar true) unif2 unif2 := by sorry
