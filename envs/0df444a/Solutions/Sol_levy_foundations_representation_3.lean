-- Prove2me | solution 3 for levy_foundations_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:39:10.110338+00:00
-- url     : https://prove2.me/submissions/6a8807c9-d032-406f-af50-8a0715c62ad0

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

/-- The exponent supplied by infinite divisibility is represented by a
Lévy–Khintchine triple via the public semigroup representation theorem. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  obtain ⟨ψ, hψ, hchar, hsemigroup⟩ :=
    levy_foundations_id_has_continuous_characteristic_exponent hμ
  obtain ⟨T, hT⟩ :=
    levy_foundations_semigroup_exponent_is_levyKhintchine ψ hψ hsemigroup
  refine ⟨T, ?_⟩
  intro ξ
  rw [hchar ξ, hT ξ]
