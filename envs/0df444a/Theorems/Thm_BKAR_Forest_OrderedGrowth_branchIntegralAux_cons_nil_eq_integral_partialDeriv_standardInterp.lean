-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
-- name    : BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:13.494748+00:00
-- url     : https://prove2.me/theorems/c3ee18ad-bf49-54c9-b946-3ff14d54d59d
-- title:
--   Ordered Growth: branch Integral Aux cons nil eq integral partial Deriv standard Interp
-- statement:
--   The Ordered Growth construction uses the branch Integral Aux cons nil eq integral partial Deriv standard Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L292-L301
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L292-L301

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegralAux top u ρ =
      ∫ t in 0..top, partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) := by sorry
