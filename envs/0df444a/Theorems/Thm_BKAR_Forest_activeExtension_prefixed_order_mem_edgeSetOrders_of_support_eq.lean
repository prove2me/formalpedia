-- Prove2me | Theorems.Thm_BKAR_Forest_activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
-- name    : BKAR.Forest.activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:21.092821+00:00
-- url     : https://prove2.me/theorems/cb537eba-6b26-5e69-8d94-2a185a5ac69d
-- title:
--   Forest: active Extension prefixed order mem edge Set Orders of support eq
-- statement:
--   At an arbitrary recursion node, appending the chosen active edge to an existing
--   canonical prefix gives a canonical order of the child support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L48-L69
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L48-L69

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
    {F : Forest V} {e : Edge V} (h : ActiveExtension F e)
    {pref : List (Edge V)} (hpref : pref.toFinset = F.edges)
    (hnodup : pref.Nodup)
    {I : ForestIndex V} (hsupport : h.forest.support = I) :
    pref ++ [e] ∈ edgeSetOrders I.edges := by sorry
