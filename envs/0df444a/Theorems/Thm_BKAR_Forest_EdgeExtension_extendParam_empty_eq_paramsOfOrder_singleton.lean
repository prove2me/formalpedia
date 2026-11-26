-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_empty_eq_paramsOfOrder_singleton
-- name    : BKAR.Forest.EdgeExtension.extendParam_empty_eq_paramsOfOrder_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:06.999801+00:00
-- url     : https://prove2.me/theorems/1b5f8e08-6dec-54cf-8ef9-b4aa00eaf68f
-- title:
--   Edge Extension: extend Param empty eq params Of Order singleton
-- statement:
--   The Edge Extension construction uses the extend Param empty eq params Of Order singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L503-L507
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L503-L507

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

theorem BKAR.Forest.EdgeExtension.extendParam_empty_eq_paramsOfOrder_singleton
    (h : EdgeExtension (Forest.empty V) F' e) (t : ℝ) :
    h.extendParam emptyParam t = F'.paramsOfOrder [e] [t] := by sorry
