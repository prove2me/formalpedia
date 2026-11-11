-- Prove2me | solution 1 for levy_foundations_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:46:48.049654+00:00
-- url     : https://prove2.me/submissions/1352004f-eff3-440e-9449-7ed3c0d9a6d7

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_id_has_continuous_characteristic_exponent
import Theorems.Thm_levy_foundations_semigroup_exponent_is_levyKhintchine

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  obtain ⟨ψ, hψcont, hμψ, hψsemigroup⟩ :=
    levy_foundations_id_has_continuous_characteristic_exponent hμ
  obtain ⟨T, hT⟩ :=
    levy_foundations_semigroup_exponent_is_levyKhintchine ψ hψcont hψsemigroup
  refine ⟨T, ?_⟩
  intro ξ
  rw [hμψ ξ, hT ξ]
