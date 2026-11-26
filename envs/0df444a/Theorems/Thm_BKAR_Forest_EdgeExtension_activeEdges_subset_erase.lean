-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_subset_erase
-- name    : BKAR.Forest.EdgeExtension.activeEdges_subset_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:59.86192+00:00
-- url     : https://prove2.me/theorems/4d2fe6c5-7ef5-559a-a26f-5dd9a42a85ab
-- title:
--   Edge Extension: active Edges subset erase
-- statement:
--   After a one-edge extension, every still-active edge was already active before,
--   and the newly inserted edge is no longer active.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L39-L51
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L39-L51

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.activeEdges_subset_erase (h : EdgeExtension F F' e₀) :
    F'.activeEdges ⊆ F.activeEdges.erase e₀ := by sorry
