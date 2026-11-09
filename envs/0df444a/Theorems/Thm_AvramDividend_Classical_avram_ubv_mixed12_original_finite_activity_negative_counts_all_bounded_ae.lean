-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:46:20.088108+00:00
-- url     : https://prove2.me/theorems/ebd98fb4-754c-46ce-a419-23a731c44d69
-- title:
--   Single almost-sure event of finite original negative jump counts on every finite horizon
-- statement:
--   For finite negative Lévy activity, on a single full-measure set the original process has finitely many intrinsic negative jumps on every bounded real-valued time horizon. Extend the already established simultaneous natural-horizon count by cofinality and monotonicity of the original marked count measure. This is needed for same-space finite-jump removal before Gaussian residual construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
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
        (Ioc 0 t ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
