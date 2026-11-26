-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:19.662001+00:00
-- url     : https://prove2.me/theorems/dda14207-1443-5b63-adf6-30060bc6bf42
-- title:
--   Forest: root Boundary Support Order Contribution nil eq zero of edges ne empty
-- statement:
--   The empty order contributes only to the empty support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L20-L28
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L20-L28

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] = 0 := by sorry
