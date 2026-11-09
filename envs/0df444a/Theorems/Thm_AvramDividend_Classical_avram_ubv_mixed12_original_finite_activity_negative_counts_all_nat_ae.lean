-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_nat_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_nat_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:27:42.684588+00:00
-- url     : https://prove2.me/theorems/e384011b-efeb-4307-913b-6a20384a31ea
-- title:
--   Original finite-activity intrinsic negative jumps are locally finite on every integer horizon almost surely
-- statement:
--   Under finite negative jump intensity, a single full-measure event supports finite original intrinsic negative jump counts on every integer horizon. This removes an uncountable exceptional-event ambiguity in constructing the same-process jump-removed Gaussian residual for the mixed finite-activity stopped verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_nat_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
