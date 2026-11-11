-- Prove2me | solution 2 for levy_foundations_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:06:50.980628+00:00
-- url     : https://prove2.me/submissions/d2511c49-c80b-4103-af8e-a7927604b3de

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_representation
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_injective
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_continuous
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_zero
import Theorems.Thm_ProbabilityTheory_eq_of_cexp_eq_of_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃! T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  obtain ⟨T, hT⟩ := levy_foundations_representation hμ
  refine ⟨T, hT, fun U hU => ?_⟩
  apply LevyFoundations.leanlevy_chat16_exponent_injective
  have hfun : LevyFoundations.exponent U = LevyFoundations.exponent T :=
    ProbabilityTheory.eq_of_cexp_eq_of_continuous
      (LevyFoundations.leanlevy_chat16_exponent_continuous U)
      (LevyFoundations.leanlevy_chat16_exponent_continuous T)
      (by rw [LevyFoundations.leanlevy_chat16_exponent_zero U,
        LevyFoundations.leanlevy_chat16_exponent_zero T])
      (fun ξ => by rw [← hU ξ, ← hT ξ])
  exact fun ξ => congrFun hfun ξ
