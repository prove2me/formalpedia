-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_cons
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:33.05706+00:00
-- url     : https://prove2.me/theorems/e02ebe80-9a55-5438-a318-c3572a9af166
-- title:
--   Ordered Growth: branch Integrand cons cons
-- statement:
--   The Ordered Growth construction uses the branch Integrand cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L198-L205
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L198-L205

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts) =
      mixedPartialList (e :: order).reverse ρ
        (G.standardInterp (tail.params (step.extendParam u t) ts)) := by sorry
