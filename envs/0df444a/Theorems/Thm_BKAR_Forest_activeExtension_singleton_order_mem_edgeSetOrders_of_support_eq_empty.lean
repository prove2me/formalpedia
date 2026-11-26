-- Prove2me | Theorems.Thm_BKAR_Forest_activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
-- name    : BKAR.Forest.activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:26.772055+00:00
-- url     : https://prove2.me/theorems/80f9d932-eb58-462d-898c-381d3b3efc14
-- title:
--   Forest: active Extension singleton order mem edge Set Orders of support eq empty
-- statement:
--   The singleton order attached to an empty-start active extension is canonical in
--   any support fiber containing that extension.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L33-L42
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L33-L42

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    {I : ForestIndex V} (hsupport : h.forest.support = I) :
    [e] ∈ edgeSetOrders I.edges := by sorry
