-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T17:03:58.204514+00:00
-- url     : https://prove2.me/theorems/3545e03a-bae3-4152-837c-57556963f4d5
-- title:
--   All original nonzero jump marks are locally finite under finite negative activity
-- statement:
--   A spectrally negative Levy process of finite total negative jump intensity has, on one probability-one event, finite original marked count of all nonzero jump marks in each bounded interval. Derive by splitting all marks into negative and nonnegative, invoking the source-exact zero nonnegative mark count and the previously proved every-bounded-horizon negative count. This supplies the finite jump support prerequisite for same-space Gaussian residual extraction in mixed verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) < ⊤ := by sorry
