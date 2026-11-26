-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_mem_activeEdges
-- name    : BKAR.Forest.ActiveExtension.mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:33.340851+00:00
-- url     : https://prove2.me/theorems/2e4ec806-4315-4cdf-961d-272ce41d4c6a
-- title:
--   Active Extension: mem active Edges
-- statement:
--   The edge of a chosen one-edge extension is active for the old forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L176-L178
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L176-L178

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.mem_activeEdges (h : ActiveExtension F e) :
    e ∈ F.activeEdges := by sorry
