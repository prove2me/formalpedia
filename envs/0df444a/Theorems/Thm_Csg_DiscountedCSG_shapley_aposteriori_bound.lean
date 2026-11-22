-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_shapley_aposteriori_bound
-- name    : Csg.DiscountedCSG.shapley_aposteriori_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:32:40.187192+00:00
-- url     : https://prove2.me/theorems/3f879305-05c7-4a0a-83ce-fe0a7b65bf94
-- title:
--   Discounted CSG: shapley aposteriori bound
-- statement:
--   A posteriori error bound: the distance to `vOpt` after `n` iterations, bounded purely by how
--       much the last step moved. This is the "stop once consecutive iterates are close" criterion, and
--       the fact `stopCond` below is built to exploit. Mirrors `bellman_aposteriori_bound`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L109-L111
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L109-L111

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.shapley_aposteriori_bound (v : S → ℝ) (n : ℕ) :
    dist (D.shapley^[n] v) D.vOpt ≤ dist (D.shapley^[n] v) (D.shapley^[n + 1] v) / (1 - D.lNN) := by sorry
