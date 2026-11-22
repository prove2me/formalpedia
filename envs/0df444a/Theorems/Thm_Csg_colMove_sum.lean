-- Prove2me | Theorems.Thm_Csg_colMove_sum
-- name    : Csg.colMove_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:54:57.915662+00:00
-- url     : https://prove2.me/theorems/3898f589-e6b7-4e1d-9a64-e91ce96c4440
-- title:
--   Csg: col Move sum
-- statement:
--   Expand a sum over all of `ColMove` into its two terms.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L127-L130
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean#L127-L130

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
set_option autoImplicit true
open Csg

theorem Csg.colMove_sum {β : Type*} [AddCommMonoid β] (f : ColMove → β) :
    ∑ a : ColMove, f a = f .c + f .d := by sorry
