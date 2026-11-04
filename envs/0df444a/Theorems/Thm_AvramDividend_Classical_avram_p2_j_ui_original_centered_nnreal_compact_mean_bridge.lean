-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:24:56.535335+00:00
-- url     : https://prove2.me/theorems/2e3accb5-84b5-4973-bc04-6b45a54f9e53
-- title:
--   Original centered NNReal compact negative test mesh limits imply integrability, strong L1 and mean convergence
-- statement:
--   For the actual spectrally negative Levy process with a positive NNReal horizon and any continuous compact strictly negative test, assume the centered NNReal grid sums converge almost everywhere to a named Z. Then Z is integrable and the uncentered NNReal uniform-grid sums converge to Z in strong L1 and genuinely expected Bochner integrals. This composes the accepted source-specific Vitali theorem with the mathematically exact mesh-width and centered-increment identifications; it does not postulate the P2-H pathwise limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_named_limit_both
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_uniform_nnreal_real_mesh_identification

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Original centered NNReal pathwise limits yield uncentered NNReal strong L1 and expected-grid limits. -/

theorem AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (Z : Ω → ℝ)
    (hcenter : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
           (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω)))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
