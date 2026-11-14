-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB53_original_BV_choose_small_mark_moment_below_physical_drift
-- name    : AvramDividend.Classical.avram_bva_capHJB53_original_BV_choose_small_mark_moment_below_physical_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:45:25.276968+00:00
-- url     : https://prove2.me/theorems/810a26cf-8f65-4b6b-b660-8732f8bebb5f
-- title:
--   Choose a source small negative-jump first-moment cutoff whose mass is below the original positive BV drift
-- statement:
--   For the actual original spectrally negative bounded variation Levy process with physical drift strictly positive, any positive cofinal sequence of mark cutoffs shrinking to zero contains a cutoff whose truncated full negative-mark first moment is strictly less than the positive drift. Source Proved 9f2b0aa3 supplies this for q=0, retaining the original Levy measure and not assuming any spatial-mask positive-part error convergence. This is exactly the absorption parameter needed by finite-cap source C1 derivative maximum bootstrap capHJB44/47.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB53_original_BV_choose_small_mark_moment_below_physical_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hd : 0 < X.drift)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∃ n : ℕ, 0 < ε n ∧
      (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) < X.drift := by sorry
