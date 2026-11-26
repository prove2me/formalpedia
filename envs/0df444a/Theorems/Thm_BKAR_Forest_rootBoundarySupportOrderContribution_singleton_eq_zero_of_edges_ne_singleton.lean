-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:10.551095+00:00
-- url     : https://prove2.me/theorems/ed49fd3e-6011-4c13-9be1-bdaa38331f02
-- title:
--   Forest: root Boundary Support Order Contribution singleton eq zero of edges ne singleton
-- statement:
--   A singleton order contributes only over the matching singleton support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L204-L227
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L204-L227

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges ≠ ({a} : Finset (Edge V))) :
    rootBoundarySupportOrderContribution choices ρ I [a] = 0 := by sorry
