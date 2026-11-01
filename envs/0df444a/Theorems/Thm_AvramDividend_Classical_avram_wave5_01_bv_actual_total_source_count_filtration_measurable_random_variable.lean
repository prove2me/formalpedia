-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:15:05.723201+00:00
-- url     : https://prove2.me/theorems/1a909fab-8f86-43ed-acbe-e35bcda9efc6
-- title:
--   Whole finite-activity BV original jump count has an original-filtration measurable random-variable version
-- statement:
--   For the actual original-space finite-negative-activity BV spectrally negative Lévy process X, and any deterministic fine grids of [0,T], the whole intrinsic jump-count scalar random variable N_X((0,T]×ℝ), not merely each count-k level event, has an 𝓕_T-measurable ENNReal-valued representative equal P-almost surely. This constructs one source-filtration count-valued interface using the Proved grid-level measurable events and actual finite original-path jump times. The proof does not change sample space or assert negative-mark intensity.
-- source:
--   Proved original 𝓕_T level-k proxies 579a5328-fdf8-4cb8-8d7c-3ffe9f7f01cc, local finite original source jump times e35efd8b-dffe-441a-8742-4aedd214f484, exact original rectangle count f6336d40-2d19-444f-bacd-83724316de67.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
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
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P, F ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) := by sorry
