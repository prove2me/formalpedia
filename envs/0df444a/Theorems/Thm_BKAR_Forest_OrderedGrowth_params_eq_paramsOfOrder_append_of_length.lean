-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_eq_paramsOfOrder_append_of_length
-- name    : BKAR.Forest.OrderedGrowth.params_eq_paramsOfOrder_append_of_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:45:35.37464+00:00
-- url     : https://prove2.me/theorems/5e527831-c0fd-4427-ab0a-51393a22c0b4
-- title:
--   Ordered Growth: params eq params Of Order append of length
-- statement:
--   If the starting forest parameters are read from an ordered prefix, then an
--   ordered growth reads the combined prefix-plus-growth parameter list in the
--   canonical `paramsOfOrder` way. The length condition rules out the fallback
--   zeroes used for malformed parameter lists.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L561-L592
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L561-L592

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
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_eq_paramsOfOrder_append_of_length
    (h : OrderedGrowth F order G) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    h.params (F.paramsOfOrder pref prefixTs) ts =
      G.paramsOfOrder (pref ++ order) (prefixTs ++ ts) := by sorry
