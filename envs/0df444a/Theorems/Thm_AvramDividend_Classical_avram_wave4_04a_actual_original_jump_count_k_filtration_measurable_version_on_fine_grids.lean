-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:26:58.050226+00:00
-- url     : https://prove2.me/theorems/579a5328-fdf8-4cb8-8d7c-3ffe9f7f01cc
-- title:
--   Actual BV Lévy intrinsic jump count level has an original-filtration horizon-measurable representative
-- statement:
--   For actual finite-negative-activity BV source X and deterministic strictly increasing grids on (0,T] whose mesh tends to zero and whose nodes remain within T, the literal original source intrinsic jump-count-k event has an explicitly constructible 𝓕 T-measurable representative modulo P-null sets. The representative is the liminf of source drift-deficient finite-grid count events. This is a genuine same-path original-filtration adaptedness bridge, not an assertion that the uncountable-time raw point-count random variable is everywhere measurable or that its predictable compensator is established.
-- source:
--   The exact original-filtration horizon-adapted grid-count helper e3cc1dec-9b47-4c1c-af52-9dc189fef9d9 is now canonically Proved (accepted candidate 20343, evidence complete). Existing original-path count-level liminf ae equivalence 6a97b834-8508-4fac-b370-7b6925caf252 is also Proved. Combine filtration-adapted grid count-k events under 𝓕 T, MeasurableSet.measurableSet_liminf, and the exact original-a.e. equivalence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_count_horizon_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (k : ℕ) :
    ∃ E : Set Ω, MeasurableSet[𝓕 T] E ∧
      (∀ᵐ ω ∂P,
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) = (k : ENNReal) ↔
          ω ∈ E) := by sorry
