-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:24.646003+00:00
-- url     : https://prove2.me/theorems/562777c1-0ce4-4fbf-94d4-43a5582886ab
-- title:
--   Ordered Growth: branch Integrand eq mixed Partial List interp With Fill of active Edges eq empty
-- statement:
--   The Ordered Growth construction uses the branch Integrand eq mixed Partial List interp With Fill of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L136-L146
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L136-L146

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) (b : ℝ)
    (hG : G.activeEdges = ∅) :
    h.branchIntegrand u ρ ts =
      mixedPartialList h.derivativeOrder ρ
        (G.interpWithFill (h.params u ts) b) := by sorry
