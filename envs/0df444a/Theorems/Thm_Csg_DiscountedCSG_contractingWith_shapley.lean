-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley
-- name    : Csg.DiscountedCSG.contractingWith_shapley
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:00.869435+00:00
-- url     : https://prove2.me/theorems/80e17315-7aab-49c3-9b00-75c17f273179
-- title:
--   Discounted CSG: contracting With shapley
-- statement:
--   The Shapley operator is a genuine contraction: Lipschitz with constant `< 1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L169-L170
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L169-L170

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

theorem Csg.DiscountedCSG.contractingWith_shapley : ContractingWith D.lNN D.shapley := by sorry
