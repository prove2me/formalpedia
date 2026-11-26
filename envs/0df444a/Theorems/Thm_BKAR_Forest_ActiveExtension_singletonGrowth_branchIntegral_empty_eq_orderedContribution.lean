-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegral_empty_eq_orderedContribution
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegral_empty_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:11.829042+00:00
-- url     : https://prove2.me/theorems/52bbb65a-95a3-5e3b-8e21-43392e8260ea
-- title:
--   Active Extension: singleton Growth branch Integral empty eq ordered Contribution
-- statement:
--   The one-edge branch grown from the empty forest is exactly the canonical
--   one-edge ordered-sector contribution for its terminal forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L675-L689
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L675-L689

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {e : Edge V}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegral_empty_eq_orderedContribution
    (h : ActiveExtension (Forest.empty V) e)
    (ρ : (Edge V → ℝ) → ℝ) :
    h.singletonGrowth.branchIntegral emptyParam ρ =
      h.forest.orderedContribution [e] ρ := by sorry
