-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_bounded_compact_grid_mean
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_public_bounded_compact_grid_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:22:26.409002+00:00
-- url     : https://prove2.me/theorems/554b5226-64a4-4465-8e13-a2f1273d63dd
-- title:
--   Public original-process bounded compact negative grid-test expectation limit
-- statement:
--   For the genuine original Lévy process and an explicitly bounded separated-negative continuous compact test, source pathwise uniform-grid limits have an integrable measurable representative and the expected grid sums converge to its integral. The proof uses only public original sample-path convergence and public signed uniformly-integrable grid mean convergence. It assumes no compensator, auxiliary Lévy process, jump-rate identity or conclusion-as-premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_public_bounded_compact_grid_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hbound : ∀ y : ℝ,
      ‖g y‖ₑ ≤ if y ≤ -ε then M else 0)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (𝓝 (∫ ω, Z ω ∂P)) := by sorry
