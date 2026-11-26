-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_congr
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:59.033544+00:00
-- url     : https://prove2.me/theorems/34ec2ca1-1f41-405e-8226-da3385d3bfbe
-- title:
--   Ordered Growth: branch Integral congr
-- statement:
--   The Ordered Growth construction uses the branch Integral congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L244-L248
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L244-L248

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_congr (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegral u ρ = h.branchIntegral v σ := by sorry
