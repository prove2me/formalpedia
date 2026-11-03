-- Prove2me | solution 1 for levy_foundations_existsPoissonPointFamily
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:39:15.53175+00:00
-- url     : https://prove2.me/submissions/e2a739d7-514f-4a4f-af1a-8994ef5fe539

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_pointFamilyLaw
import Theorems.Thm_levy_foundations_prmPieceLawProb

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {E : Type} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E),
      IsProbabilityMeasure μ ∧
        LevyFoundations.IsPoissonPointFamily K X m μ  := by
  have hprob : ∀ i, IsProbabilityMeasure (LevyFoundations.pointFamilyLaw m i) := by
    rintro (k | ⟨k, n⟩)
    · change IsProbabilityMeasure
        (poissonMeasure (m (LevyFoundations.prmPiece m k)).toNNReal)
      infer_instance
    · change IsProbabilityMeasure (LevyFoundations.prmPieceLaw m k)
      exact levy_foundations_prmPieceLawProb m k
  letI : ∀ i, IsProbabilityMeasure (LevyFoundations.pointFamilyLaw m i) := hprob
  obtain ⟨Ω, mΩ, μ, Z, hmeas, hlaw, hindep, hμ⟩ :=
    exists_hasLaw_indepFun (LevyFoundations.pointFamilyIndexType E)
      (LevyFoundations.pointFamilyLaw m)
  refine ⟨Ω, mΩ, μ, fun k => Z (Sum.inl k),
    fun k n => Z (Sum.inr (k, n)), hμ, ?_⟩
  have hcomb :
      LevyFoundations.pointFamilyCombined
        (fun k => Z (Sum.inl k))
        (fun k n => Z (Sum.inr (k, n))) = Z := by
    funext i ω
    rcases i with k | p
    · rfl
    · rfl
  exact {
    measurable_count := fun k => hmeas (Sum.inl k)
    measurable_point := fun k n => hmeas (Sum.inr (k, n))
    indep := by rw [hcomb]; exact hindep
    law_count := fun k => hlaw (Sum.inl k)
    law_point := fun k n => hlaw (Sum.inr (k, n))
  }
