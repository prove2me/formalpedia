-- Prove2me | solution 1 for levy_foundations_semigroup_exponent_conditionally_negative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:16:16.614291+00:00
-- url     : https://prove2.me/submissions/c62fac0b-4938-4918-826b-5bb07a60cd5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_posDefCharFun
import Theorems.Thm_levy_foundations_exp_posdef_implies_cnd

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Reduce the semigroup generator CND property to the Schoenberg
positive-definite exponential derivative criterion. -/
theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by
  apply levy_foundations_exp_posdef_implies_cnd ψ
  intro t ht
  obtain ⟨ν, hν, hchar⟩ := hsemigroup t ht
  let p : ProbabilityMeasure ℝ := ⟨ν, hν⟩
  have heq :
      (fun ξ : ℝ => Complex.exp ((t : ℂ) * ψ ξ)) =
        (fun ξ : ℝ => charFun ν ξ) := by
    funext ξ
    exact (hchar ξ).symm
  rw [heq]
  simpa [p] using levy_foundations_posDefCharFun p
