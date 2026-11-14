-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
-- name    : AvramDividend.Classical.avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:39:05.529421+00:00
-- url     : https://prove2.me/theorems/beb20342-b5b1-4a36-a819-dad0e9900a91
-- title:
--   Original BV zero-cutoff Gaussian residual equals the full compensated negative small-mark source path
-- statement:
--   For an original finite-negative-activity bounded-variation Lévy process, the zero-cutoff residual consists exactly of the full compensated negative small-mark field, with no Gaussian source residual. It follows from the PROVED original BV raw negative jumps-removed identity and actual marked-jump separation into large marks and compensated small marks, including drift correction. This physically exact identity is the missing source bridge from sigma-zero BV to vanishing original Gaussian cutoff limit.
-- source:
--   Proved BV original raw jump removed residual identity 79a63ca0, original jump measure path construction ja18t, source drift identity c minus small mark first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hBV : X.BoundedVariation)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        Jsmall t ω := by sorry
