-- Prove2me | Theorems.Thm_Csg_cbState_sum
-- name    : Csg.cbState_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:57:21.959781+00:00
-- url     : https://prove2.me/theorems/9e9b0ecb-679a-428a-b001-31478aae5d42
-- title:
--   Csg: cb State sum
-- statement:
--   Expand a sum over all of `CBState` into its five terms.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L89-L95
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L89-L95

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.cbState_sum {β : Type*} [AddCommMonoid β] (f : CBState → β) :
    ∑ s : CBState, f s = f .t1 + f .t2 + f .t3 + f .t4 + f .t5 := by sorry
