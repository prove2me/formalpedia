-- Prove2me | Theorems.Thm_Csg_cbCoin_apply_right
-- name    : Csg.cbCoin_apply_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:03:52.949549+00:00
-- url     : https://prove2.me/theorems/e8361256-237e-4b82-96c8-fb4697c49f31
-- title:
--   Csg: cb Coin apply right
-- statement:
--   The Csg construction uses the cb Coin apply right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L144-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L144-L149

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbCoin_apply_right (x y : CBState) (hxy : x ≠ y) :
    cbCoin x y hxy y = (2 : ENNReal)⁻¹ := by sorry
