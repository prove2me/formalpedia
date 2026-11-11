-- Prove2me | solution 3 for levy_foundations_public_semigroup_levy_measure_extraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:47:35.973292+00:00
-- url     : https://prove2.me/submissions/6dfb5322-89ac-4d14-9cd7-71b59225dac0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_tilted_bounds
import Theorems.Thm_levy_foundations_public_weighted_prokhorov_untilting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The semigroup source estimates and the generic weighted Prokhorov
extraction assemble to the common Lévy-measure subsequence. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (ν : Measure ℝ), IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
        Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
        (∀ (f : BoundedContinuousFunction ℝ ℝ),
          (∃ r > 0, ∀ x, |x| < r → f x = 0) →
          Tendsto (fun n => (t_seq n).val⁻¹ *
              ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
            atTop (𝓝 (∫ x, f x ∂ν))) := by
  obtain ⟨t_seq, ht, ⟨C, hC⟩, htail⟩ :=
    levy_foundations_public_semigroup_tilted_bounds S
  let μ : ℕ → Measure ℝ := fun n => (S.measure (t_seq n) : Measure ℝ)
  let a : ℕ → ℝ := fun n => (t_seq n).val⁻¹
  have hprob : ∀ n, IsProbabilityMeasure (μ n) := by
    intro n
    exact (S.measure (t_seq n)).prop
  have ha : ∀ n, 0 < a n := by
    intro n
    exact inv_pos.mpr (t_seq n).prop
  have hMass : ∃ C : ℝ, ∀ n,
      a n * ∫ x, min (1 : ℝ) (x ^ 2) ∂(μ n) ≤ C :=
    ⟨C, hC⟩
  have hTail : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ n, a n * ((μ n) (largeSet R)).toReal ≤ δ := by
    intro δ hδ
    obtain ⟨R, hR, hRn⟩ := htail δ hδ
    exact ⟨R, hR, hRn⟩
  obtain ⟨ν, hν, φ, hφ, hconv⟩ :=
    levy_foundations_public_weighted_prokhorov_untilting
      μ a hprob ha hMass hTail
  refine ⟨ν, hν, (fun n => t_seq (φ n)),
    ht.comp hφ.tendsto_atTop, ?_⟩
  intro f hf
  simpa only [μ, a] using hconv f hf
