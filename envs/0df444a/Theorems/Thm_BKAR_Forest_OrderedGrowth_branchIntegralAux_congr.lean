-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_congr
-- name    : BKAR.Forest.OrderedGrowth.branchIntegralAux_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:13.212111+00:00
-- url     : https://prove2.me/theorems/7c924b5c-35ea-47a4-82fd-149c55c442e7
-- title:
--   Ordered Growth: branch Integral Aux congr
-- statement:
--   The Ordered Growth construction uses the branch Integral Aux congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L237-L242
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L237-L242

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegralAux_congr (top : ℝ) (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v σ := by sorry
