-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:10.080393+00:00
-- url     : https://prove2.me/theorems/47ea3de5-9375-582c-b2e7-ab1726b60ddb
-- title:
--   Ordered Growth: branch Integral Aux cons eq integral tail partial Deriv
-- statement:
--   The Ordered Growth construction uses the branch Integral Aux cons eq integral tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L276-L290
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L276-L290

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

theorem BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) := by sorry
