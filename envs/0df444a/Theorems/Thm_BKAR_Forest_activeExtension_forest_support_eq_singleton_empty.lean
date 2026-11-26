-- Prove2me | Theorems.Thm_BKAR_Forest_activeExtension_forest_support_eq_singleton_empty
-- name    : BKAR.Forest.activeExtension_forest_support_eq_singleton_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:42.229202+00:00
-- url     : https://prove2.me/theorems/e037b6f8-aabe-563f-81b1-d539c36507c9
-- title:
--   Forest: active Extension forest support eq singleton empty
-- statement:
--   A one-edge active extension from the empty forest has singleton support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L21-L27
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L21-L27

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeExtension_forest_support_eq_singleton_empty
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e) :
    h.forest.support = ForestIndex.singleton e := by sorry
