-- Prove2me | solution 1 for levy_foundations_public_semigroup_drift_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:53:38.136399+00:00
-- url     : https://prove2.me/submissions/5a9c7a8e-e76f-4592-8d3a-a1ab5719fe84

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_drift_eventually_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology

/-- Compactness extracts a drift limit once the substantive semigroup
first-moment bound is supplied by the public analytic child. -/
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
  let a : ℕ → ℝ := fun n =>
    (t_seq n).val⁻¹ *
      ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)
  have ha : ∀ᶠ n in atTop, a n ∈ Set.Icc (-C) C := hC
  obtain ⟨b, _, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq' ha.frequently
  exact ⟨b, φ, hφ, hlim⟩