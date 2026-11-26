-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_append_singleton
-- name    : BKAR.Forest.EdgeExtension.extendParam_eq_paramsOfOrder_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:22.527864+00:00
-- url     : https://prove2.me/theorems/adfe58ba-6de2-420a-8c87-d3a6a30d1f7b
-- title:
--   Edge Extension: extend Param eq params Of Order append singleton
-- statement:
--   Appending one newly-added edge to an existing order is compatible with the
--   recursive one-edge parameter extension.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L513-L547
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L513-L547

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
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.Forest.EdgeExtension.extendParam_eq_paramsOfOrder_append_singleton
    (h : EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ) (t : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    h.extendParam (F.paramsOfOrder pref prefixTs) t =
      F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t]) := by sorry
