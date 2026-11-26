-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_empty
-- name    : BKAR.Forest.orderedContribution_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:28.242295+00:00
-- url     : https://prove2.me/theorems/1974b757-7ac4-5382-9d75-fde11248e9ad
-- title:
--   Forest: ordered Contribution empty
-- statement:
--   The ordered-simplex contribution of the empty forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L620-L624
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L620-L624

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

theorem BKAR.Forest.orderedContribution_empty (ρ : (Edge V → ℝ) → ℝ) :
    (Forest.empty V).orderedContribution [] ρ = ρ zeroConfig := by sorry
