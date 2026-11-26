-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_initial
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:23.485799+00:00
-- url     : https://prove2.me/theorems/0a6b66c6-370c-5787-ae42-8e77cb296a19
-- title:
--   Ordered Growth: branch Point initial
-- statement:
--   A branch point agrees with the starting parameter on every starting edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L76-L82
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L76-L82

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_initial (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.branchPoint u ts e.val = u e := by sorry
