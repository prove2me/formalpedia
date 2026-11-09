-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_jump_tsum_finite_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_jump_tsum_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T19:11:26.756184+00:00
-- url     : https://prove2.me/theorems/a55466fc-e14b-4cb3-aff7-e26e926ebdb0
-- title:
--   Original finite-activity jump-size tsum equals finite original jump-time sum on all bounded horizons
-- statement:
--   For the same original spectrally negative Levy process under finite negative Levy intensity, there is a common full-measure event on which every bounded horizon has a finite exact set of nonzero original jump times and the time-truncated sum of original jump sizes equals the finite sum over that set. This converts the intrinsic infinite jump series used by the original stopped Ito-Meyer reserve decomposition into a finite pathwise sum without changing the process or its filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_jump_tsum_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) =
        ∑ u ∈ F, (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
