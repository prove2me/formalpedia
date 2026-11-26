-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc
-- name    : BKAR.Forest.OrderedGrowth.params_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:42.051313+00:00
-- url     : https://prove2.me/theorems/b43d70d9-89db-4c08-b247-011fb72f3b53
-- title:
--   Ordered Growth: params mem Icc
-- statement:
--   The Ordered Growth construction uses the params mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L86-L106
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L86-L106

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_mem_Icc (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : ∀ t ∈ ts, 0 ≤ t ∧ t ≤ 1) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 := by sorry
