-- Prove2me | solution 2 for levy_foundations_public_semigroup_drift_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:57:28.634846+00:00
-- url     : https://prove2.me/submissions/6ced7b83-5267-44e0-bf0d-26bb3e2da965

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_drift_eventually_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Extract a convergent subsequence from the eventually bounded scaled drift. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ b : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n =>
        (t_seq (φ n)).val⁻¹ *
          ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq (φ n)) : Measure ℝ))
        atTop (𝓝 b) := by
  obtain ⟨C, hC⟩ :=
    levy_foundations_public_semigroup_drift_eventually_bounded S hr hr1 ht
  obtain ⟨b, _hb, φ, hφ, hlim⟩ :=
    isCompact_Icc.tendsto_subseq' hC.frequently
  exact ⟨b, φ, hφ, hlim⟩
