-- Prove2me | solution 2 for levy_foundations_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:47:31.893135+00:00
-- url     : https://prove2.me/submissions/f58365cb-736d-4170-b76b-d97a868f4c68

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

/-- Representation follows from the convolution-semigroup logarithm
and the Lévy–Khintchine characterisation of continuous exponents. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  obtain ⟨ψ, hψcont, hchar, hsemigroup⟩ :=
    levy_foundations_id_has_continuous_characteristic_exponent hμ
  obtain ⟨T, hT⟩ :=
    levy_foundations_semigroup_exponent_is_levyKhintchine
      ψ hψcont hsemigroup
  refine ⟨T, ?_⟩
  intro ξ
  calc
    charFun μ ξ = Complex.exp (ψ ξ) := hchar ξ
    _ = Complex.exp (LevyFoundations.exponent T ξ) := by rw [hT ξ]
