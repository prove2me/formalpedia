-- Prove2me | solution 1 for levy_foundations_public_weighted_prokhorov_untilting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:48:26.768693+00:00
-- url     : https://prove2.me/submissions/d8782897-455e-45fc-ae8c-93dc17c621af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_weighted_prokhorov_compactness
import Theorems.Thm_levy_foundations_public_finite_measure_untilting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Extract the finite weak limit once, and remove the quadratic tilt away
from the origin. The two imported obligations are independent. -/
theorem solution
    (μ : ℕ → Measure ℝ) (a : ℕ → ℝ)
    (hprob : ∀ n, IsProbabilityMeasure (μ n))
    (ha : ∀ n, 0 < a n)
    (hMass : ∃ C : ℝ, ∀ n,
      a n * ∫ x, min (1 : ℝ) (x ^ 2) ∂(μ n) ≤ C)
    (hTail : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ n, a n * ((μ n) (largeSet R)).toReal ≤ δ) :
    ∃ ν : Measure ℝ, IsLevyMeasure ν ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ f : BoundedContinuousFunction ℝ ℝ,
          (∃ r > 0, ∀ x, |x| < r → f x = 0) →
          Tendsto (fun n => a (φ n) * ∫ x, f x ∂(μ (φ n)))
            atTop (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨η, hη, φ, hφ, hconv⟩ :=
    levy_foundations_public_weighted_prokhorov_compactness
      μ a hprob ha hMass hTail
  letI : IsFiniteMeasure η := hη
  obtain ⟨ν, hν, huntilt⟩ :=
    levy_foundations_public_finite_measure_untilting η
  refine ⟨ν, hν, φ, hφ, ?_⟩
  intro f hf
  obtain ⟨g, hg0, hfg, hint⟩ := huntilt f hf
  have hint_eq (n : ℕ) :
      (∫ x, f x ∂(μ (φ n))) =
        ∫ x, min (1 : ℝ) (x ^ 2) * g x ∂(μ (φ n)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => hfg x)
  have hfun :
      (fun n => a (φ n) * ∫ x, f x ∂(μ (φ n))) =
      (fun n => a (φ n) * ∫ x, min (1 : ℝ) (x ^ 2) * g x ∂(μ (φ n))) := by
    funext n
    rw [hint_eq n]
  rw [hfun, hint]
  exact hconv g hg0
