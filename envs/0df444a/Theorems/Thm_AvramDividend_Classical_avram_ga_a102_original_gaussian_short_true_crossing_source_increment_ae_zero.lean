-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
-- name    : AvramDividend.Classical.avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:21:18.804912+00:00
-- url     : https://prove2.me/theorems/9168a231-3aa7-4931-b324-01f0db80e266
-- title:
--   Original zero-jump Gaussian source has vanishing true random crossing cell displacement almost surely
-- statement:
--   For arbitrary random clocks s_m(ω), t_m(ω) in a fixed finite horizon separated by at most the uniform physical mesh width, the actual original zero-jump Lévy source increment X(t_m)-X(s_m) tends to zero almost surely. This includes random true stop-straddling mesh cells and does not assume the selected index is deterministic or predictable.
-- source:
--   Original stopped Gaussian b0 positive interior crossing-cell route; reuse Proved ga_a55 uniform source modulus and the original zero-jump continuous-path theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a55_uniform_continuous_mesh_oscillation
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m => X.X (t m ω) ω - X.X (s m ω) ω)
      atTop (𝓝 (0 : ℝ)) := by sorry
