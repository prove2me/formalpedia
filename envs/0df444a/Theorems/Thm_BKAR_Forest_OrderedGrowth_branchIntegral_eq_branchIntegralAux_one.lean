-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_eq_branchIntegralAux_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:01.589818+00:00
-- url     : https://prove2.me/theorems/36c9a82c-2543-42d2-8d39-6dc716ffb09f
-- title:
--   Ordered Growth: branch Integral eq branch Integral Aux one
-- statement:
--   The Ordered Growth construction uses the branch Integral eq branch Integral Aux one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L232-L235
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L232-L235

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_eq_branchIntegralAux_one (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    h.branchIntegral u ρ = h.branchIntegralAux 1 u ρ := by sorry
