-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_def_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:38.533188+00:00
-- url     : https://prove2.me/theorems/e832559a-f127-56bb-91c2-ca49914d8436
-- title:
--   Ordered Growth: branch Integrand def standard Interp
-- statement:
--   The Ordered Growth construction uses the branch Integrand def standard Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L166-L170
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L166-L170

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_def_standardInterp (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    h.branchIntegrand u ρ ts =
      mixedPartialList order.reverse ρ (G.standardInterp (h.params u ts)) := by sorry
