-- Prove2me | Theorems.Thm_Csg_cbCoin_apply_left
-- name    : Csg.cbCoin_apply_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:03:29.368957+00:00
-- url     : https://prove2.me/theorems/c2aa1b25-fbac-4448-891e-c48e38e86ed4
-- title:
--   Csg: cb Coin apply left
-- statement:
--   The Csg construction uses the cb Coin apply left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L137-L142
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L137-L142

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbCoin_apply_left (x y : CBState) (hxy : x ≠ y) :
    cbCoin x y hxy x = (2 : ENNReal)⁻¹ := by sorry
