-- Prove2me | Theorems.Thm_Csg_cbCoin_apply_other
-- name    : Csg.cbCoin_apply_other
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:03:48.357835+00:00
-- url     : https://prove2.me/theorems/96c6e7a3-356d-4458-9e79-c71cfca13fc7
-- title:
--   Csg: cb Coin apply other
-- statement:
--   The Csg construction uses the cb Coin apply other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L151-L155
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L151-L155

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbCoin_apply_other (x y z : CBState) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    cbCoin x y hxy z = 0 := by sorry
