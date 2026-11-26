-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons
-- name    : BKAR.Forest.OrderedGrowth.branchIntegralAux_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:05.078433+00:00
-- url     : https://prove2.me/theorems/15b409fd-d0af-4766-a751-d4cc1cb1d4be
-- title:
--   Ordered Growth: branch Integral Aux cons
-- statement:
--   The Ordered Growth construction uses the branch Integral Aux cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L265-L274
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L265-L274

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

theorem BKAR.Forest.OrderedGrowth.branchIntegralAux_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order
          (fun ts =>
            (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts)) := by sorry
