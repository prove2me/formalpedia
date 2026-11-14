-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_nojump_zero_nu_smallband_identically_zero
-- name    : AvramDividend.Classical.avram_a22_original_nojump_zero_nu_smallband_identically_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:49:33.367203+00:00
-- url     : https://prove2.me/theorems/bd83c420-6506-4661-b4a2-900f877a4f6f
-- title:
--   Original compensated negative smallband vanishes on a truly jumpless zero-nu source path
-- statement:
--   For an original spectrally negative Levy process with zero negative Levy measure and one specific original sample path with zero actual jump at every strictly positive time, its physical finite cutoff compensated small negative jump integral is identically zero at every horizon and band index. No new noise, measure, filtration, or independent process.
-- source:
--   Original mission physical compensated source definition, plus pathwise empty actual jump-time support and zero compensator. Kyprianou Levy-Ito chapter 2, zero intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_nojump_zero_nu_smallband_identically_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (n : ℕ) (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω = 0 := by sorry
