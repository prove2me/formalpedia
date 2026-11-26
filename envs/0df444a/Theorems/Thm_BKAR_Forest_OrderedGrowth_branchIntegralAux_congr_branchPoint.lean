-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_congr_branchPoint
-- name    : BKAR.Forest.OrderedGrowth.branchIntegralAux_congr_branchPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:34.154749+00:00
-- url     : https://prove2.me/theorems/3c91f4fa-eb8c-579a-88f2-f77ae21fa5ea
-- title:
--   Ordered Growth: branch Integral Aux congr branch Point
-- statement:
--   The Ordered Growth construction uses the branch Integral Aux congr branch Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L250-L256
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L250-L256

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegralAux_congr_branchPoint (top : ℝ)
    (h : OrderedGrowth F order G) (u v : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v ρ := by sorry
