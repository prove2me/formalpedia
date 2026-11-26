-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_cons_eq_tail_partialDeriv
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_cons_cons_eq_tail_partialDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:08.256736+00:00
-- url     : https://prove2.me/theorems/153352fa-5f5f-4cc4-8123-e5870504bd0c
-- title:
--   Ordered Growth: branch Integrand cons cons eq tail partial Deriv
-- statement:
--   The Ordered Growth construction uses the branch Integrand cons cons eq tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L207-L216
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L207-L216

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_cons_cons_eq_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e) (tail : OrderedGrowth F' order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts) =
      tail.branchIntegrand (step.extendParam u t) (partialDeriv e ρ) ts := by sorry
