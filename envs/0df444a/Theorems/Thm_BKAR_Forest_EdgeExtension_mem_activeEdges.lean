-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_mem_activeEdges
-- name    : BKAR.Forest.EdgeExtension.mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:42.278157+00:00
-- url     : https://prove2.me/theorems/61756f5f-92c0-5b74-a613-f0567e690f1b
-- title:
--   Edge Extension: mem active Edges
-- statement:
--   The edge added by an extension is active for the old forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L27-L33
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L27-L33

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

theorem BKAR.Forest.EdgeExtension.mem_activeEdges (h : EdgeExtension F F' e₀) :
    e₀ ∈ F.activeEdges := by sorry
