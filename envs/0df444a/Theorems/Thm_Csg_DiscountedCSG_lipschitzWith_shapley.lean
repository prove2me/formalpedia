-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_lipschitzWith_shapley
-- name    : Csg.DiscountedCSG.lipschitzWith_shapley
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:23.017887+00:00
-- url     : https://prove2.me/theorems/bd4a1ae7-806e-4916-8413-9276a4d6e3aa
-- title:
--   Discounted CSG: lipschitz With shapley
-- statement:
--   `shapley_contracting` restated in the `edist`-based `LipschitzWith` vocabulary that
--       `ContractingWith` is built on.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L165-L166
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L165-L166

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.lipschitzWith_shapley : LipschitzWith D.lNN D.shapley := by sorry
