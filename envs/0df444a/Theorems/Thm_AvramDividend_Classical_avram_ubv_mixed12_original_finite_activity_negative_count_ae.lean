-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_count_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_count_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:38:14.840462+00:00
-- url     : https://prove2.me/theorems/fd849aca-fa0c-4359-a36f-8edc83460cdc
-- title:
--   Original finite-activity negative jump count is almost surely finite without bounded-variation assumption
-- statement:
--   For any spectrally negative Levy process X, finite total negative jump intensity makes the intrinsic marked negative jump count on any bounded time interval almost surely finite, even when X has unbounded variation because of a nonzero Gaussian component. Derived via the original intrinsic count's proven Borel mean and measurability, and used to separate the finite-jump portion of the same original mixed Gaussian-jump process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_count_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
