-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_cons
-- name    : BKAR.Forest.EdgeExtension.extendParam_eq_paramsOfOrder_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:04.827158+00:00
-- url     : https://prove2.me/theorems/4e655359-21c9-5807-985c-94334d14f5b0
-- title:
--   Edge Extension: extend Param eq params Of Order cons
-- statement:
--   The Edge Extension construction uses the extend Param eq params Of Order cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L487-L501
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L487-L501

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

theorem BKAR.Forest.EdgeExtension.extendParam_eq_paramsOfOrder_cons
    (h : EdgeExtension F F' e) (order : List (Edge V)) (ts : List ℝ)
    (u : F.EdgeParam → ℝ) (t : ℝ)
    (hu : u = F.paramsOfOrder order ts) :
    h.extendParam u t = F'.paramsOfOrder (e :: order) (t :: ts) := by sorry
