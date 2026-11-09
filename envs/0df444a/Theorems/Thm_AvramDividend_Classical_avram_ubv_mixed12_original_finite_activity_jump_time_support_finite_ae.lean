-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:06:00.613018+00:00
-- url     : https://prove2.me/theorems/1e50b68a-ebdb-4d20-b58f-de2bab42874d
-- title:
--   Actual nonzero jump times are locally finite on the original finite-activity process
-- statement:
--   Almost surely on one common event, the set of actual nonzero jump times of the original spectrally negative Levy process is finite on each bounded horizon, under finite total negative Levy intensity. Convert the previously proved finite intrinsic marked count to a finite set using the measurable original jump-mark map and the injective time coordinate. This is a prerequisite for same-space finite-jump subtraction and Gaussian residual extraction in mixed dividend verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}.Finite := by sorry
