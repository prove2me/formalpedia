-- Prove2me | solution 2 for levy_foundations_public_semigroup_levy_measure_extraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:26:28.874921+00:00
-- url     : https://prove2.me/submissions/ebf3d84f-007b-4d18-ab5c-b891b3843538
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_canonical_tilted_measure
import Theorems.Thm_levy_foundations_public_untilt_canonical_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Extract the canonical tilted limit, then untilt it on the same time sequence. -/
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
  obtain ⟨η, hη, t_seq, ht, hconv⟩ :=
    levy_foundations_public_canonical_tilted_measure S
  obtain ⟨ν, hν, hjump⟩ :=
    levy_foundations_public_untilt_canonical_measure S η hη t_seq ht hconv
  exact ⟨ν, hν, t_seq, ht, hjump⟩
