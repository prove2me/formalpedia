-- Prove2me | Theorems.Thm_Csg_cbCSG_coBuchiOp_lfp_eq
-- name    : Csg.cbCSG_coBuchiOp_lfp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:03:00.19456+00:00
-- url     : https://prove2.me/theorems/c52d5b87-2694-4e55-92a3-2e8c9cfb2c66
-- title:
--   Csg: cb CSG co Buchi Op lfp eq
-- statement:
--   **The payoff.** `⟨1⟩◇□U`, computed on Fig. 1, matches the paper's Example 3 exactly: `1` at
--       `t1`, `2/3` at `t2`, `1/3` at `t3`, `0` at `t4`/`t5`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L612-L634
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L612-L634

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbCSG_coBuchiOp_lfp_eq : (cbCSG.coBuchiOp cbU cbR_zero).lfp = cbVStar := by sorry
