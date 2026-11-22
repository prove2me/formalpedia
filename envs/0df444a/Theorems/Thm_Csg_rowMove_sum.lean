-- Prove2me | Theorems.Thm_Csg_rowMove_sum
-- name    : Csg.rowMove_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:32.876816+00:00
-- url     : https://prove2.me/theorems/fa62e577-8402-4015-8f68-75d1191ae8db
-- title:
--   Csg: row Move sum
-- statement:
--   Expand a sum over all of `RowMove` into its two terms, matching `IntrusionDetection.lean`'s
--       `policyAction_sum` idiom.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L110-L113
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L110-L113

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.rowMove_sum {β : Type*} [AddCommMonoid β] (f : RowMove → β) :
    ∑ a : RowMove, f a = f .b + f .d := by sorry
