-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_congr
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:38:47.831853+00:00
-- url     : https://prove2.me/theorems/c2c27d33-c155-578c-9970-b593ebe42cf4
-- title:
--   Ordered Growth: branch Integrand congr
-- statement:
--   The Ordered Growth construction uses the branch Integrand congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L179-L184
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L179-L184

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_congr (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegrand u ρ = h.branchIntegrand v σ := by sorry
