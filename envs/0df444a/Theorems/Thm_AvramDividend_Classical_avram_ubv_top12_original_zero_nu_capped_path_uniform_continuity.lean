-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:28:30.502518+00:00
-- url     : https://prove2.me/theorems/70cb0577-a36c-4f52-99b4-bfb6f74cc172
-- title:
--   Original zero-jump Lévy path is uniformly continuous on each finite horizon almost surely
-- statement:
--   For the exact spectrally negative Lévy process whose jump intensity is zero, the sample path is uniformly continuous on any fixed finite positive-time interval almost surely. The pathwise compact-horizon modulus supplies the mesh-oscillation input for the original Gaussian Itô Taylor remainder without a spatial cap.
-- source:
--   Original-process public Proved b462a147-31fd-4ac5-9489-822eafbfc3c0 yields almost-sure path continuity. Pinned Mathlib IsCompact.uniformContinuousOn_of_continuous applies to the compact nonnegative time interval. Intended for source-exact stopped Gaussian refining-grid convergence before 249c532d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, UniformContinuousOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 T) := by sorry
