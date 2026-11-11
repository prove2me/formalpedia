-- Prove2me | solution 3 for levy_foundations_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:52:35.253898+00:00
-- url     : https://prove2.me/submissions/6e375992-2729-4300-bc56-4e1f2e004f29

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_id_has_continuous_characteristic_exponent
import Theorems.Thm_levy_foundations_semigroup_exponent_is_levyKhintchine
import Theorems.Thm_levy_foundations_converse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Directly reduce M7 to the continuous semigroup logarithm and the
Lévy–Khintchine representation of its generator. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    LevyFoundations.isInfinitelyDivisible μ ↔
      ∃ T : LevyFoundations.LevyKhintchineTriple,
        ∀ ξ : ℝ, charFun μ ξ =
          Complex.exp (LevyFoundations.exponent T ξ) := by
  constructor
  · intro hμ
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
  · rintro ⟨T, hT⟩
    obtain ⟨ν, hνprob, hνdiv, hνcf⟩ := levy_foundations_converse T
    haveI : IsProbabilityMeasure ν := hνprob
    have hμν : μ = ν := by
      apply Measure.ext_of_charFun
      funext ξ
      rw [hT ξ, hνcf ξ]
    rw [hμν]
    exact hνdiv
