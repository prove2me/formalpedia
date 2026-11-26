-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.ActiveExtension.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:22.148752+00:00
-- url     : https://prove2.me/theorems/9ac99339-32b1-4806-addc-945f90ade3b2
-- title:
--   Active Extension: cons Growth branch Integral Aux eq integral tail partial Deriv
-- statement:
--   The Active Extension construction uses the cons Growth branch Integral Aux eq integral tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L78-L86
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L78-L86

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.ActiveExtension.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (h : ActiveExtension F e) (tail : OrderedGrowth h.forest order G)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) := by sorry
