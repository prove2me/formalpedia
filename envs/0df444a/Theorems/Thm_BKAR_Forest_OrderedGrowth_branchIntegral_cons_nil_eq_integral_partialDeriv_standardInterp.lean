-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:12.313562+00:00
-- url     : https://prove2.me/theorems/5b61c856-37d2-5bd7-8962-4732283a3577
-- title:
--   Ordered Growth: branch Integral cons nil eq integral partial Deriv standard Interp
-- statement:
--   The Ordered Growth construction uses the branch Integral cons nil eq integral partial Deriv standard Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L326-L333
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L326-L333

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) := by sorry
