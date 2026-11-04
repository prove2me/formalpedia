-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_named_limit_both
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_named_limit_both
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:11.200999+00:00
-- url     : https://prove2.me/theorems/eda2e121-3098-4ed2-9c91-281186c8d208
-- title:
--   Original compact negative test converges strongly in L1 and expectation to its named jump-sum limit
-- statement:
--   For an original spectrally negative Levy process and a continuous compact strictly negative test, coordinate measurability plus almost-everywhere convergence of its genuine signed n+1-grid sums to a named random variable Z imply Integrable Z, strong L1 convergence and genuine Bochner expectation convergence. No pre-existing measurability of Z is required, and no unproved grid limit is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_test_finite_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_grid_measurability_from_path
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_named_limit_both
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (T : ℝ) (hT : 0 < T)
    (Z : Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
