-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_first
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:26.453603+00:00
-- url     : https://prove2.me/theorems/b2129130-bd82-42ec-a22d-81b68c81ce08
-- title:
--   Ordered Growth: branch Point first
-- statement:
--   The first edge of a nonempty branch receives the first simplex parameter.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L90-L96
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L90-L96

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_first (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.branchPoint u (t :: ts) e = t := by sorry
