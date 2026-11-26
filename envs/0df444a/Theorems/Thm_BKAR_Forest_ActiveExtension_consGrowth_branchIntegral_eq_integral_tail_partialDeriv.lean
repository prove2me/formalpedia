-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchIntegral_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.ActiveExtension.consGrowth_branchIntegral_eq_integral_tail_partialDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:49.740408+00:00
-- url     : https://prove2.me/theorems/14b9e42e-3336-5b14-806c-3a1480e581f5
-- title:
--   Active Extension: cons Growth branch Integral eq integral tail partial Deriv
-- statement:
--   The Active Extension construction uses the cons Growth branch Integral eq integral tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L88-L95
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L88-L95

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

theorem BKAR.Forest.ActiveExtension.consGrowth_branchIntegral_eq_integral_tail_partialDeriv
    (h : ActiveExtension F e) (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) := by sorry
