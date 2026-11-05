-- Prove2me | solution 1 for levy_foundations_compoundPoissonDriverExists
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:36.679652+00:00
-- url     : https://prove2.me/submissions/e9adbf41-0811-4885-b7bc-217e57e5fcb2

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_levy_foundations_isCadlag
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Interval

theorem solution
    (r : ℝ≥0) (hr : 0 < r) (ν' : Measure ℝ) [IsProbabilityMeasure ν'] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ),
       IsProbabilityMeasure μ ∧ LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ := by
  have hexp : IsProbabilityMeasure (expMeasure (r : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast hr)
  have hinst : ∀ i : ℕ ⊕ ℕ, IsProbabilityMeasure
      (Sum.elim (fun _ : ℕ => expMeasure (r : ℝ)) (fun _ : ℕ => ν') i) := by
    intro i; cases i <;> simpa
  obtain ⟨Ω, mΩ, P, X, hmeas, hlaw, hind, hP⟩ :=
    exists_hasLaw_indepFun (ι := ℕ ⊕ ℕ) (fun _ => ℝ)
      (fun i => Sum.elim (fun _ : ℕ => expMeasure (r : ℝ)) (fun _ : ℕ => ν') i)
  have he : Sum.elim (fun n => X (Sum.inl n)) (fun n => X (Sum.inr n)) = X := by
    funext i; cases i <;> rfl
  refine ⟨Ω, mΩ, P, fun n => X (Sum.inl n), fun n => X (Sum.inr n), hP, ?_⟩
  exact ⟨fun n => hmeas _, fun n => hmeas _, by rw [he]; exact hind,
    fun n => hlaw (Sum.inl n), fun n => hlaw (Sum.inr n)⟩
