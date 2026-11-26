-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_cons_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_cons_eq_integral_tail_partialDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:40:06.464564+00:00
-- url     : https://prove2.me/theorems/6740aca0-1390-5c19-990b-648c8471a53c
-- title:
--   Ordered Growth: branch Integral cons eq integral tail partial Deriv
-- statement:
--   The Ordered Growth construction uses the branch Integral cons eq integral tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L314-L324
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L314-L324

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

theorem BKAR.Forest.OrderedGrowth.branchIntegral_cons_eq_integral_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) := by sorry
