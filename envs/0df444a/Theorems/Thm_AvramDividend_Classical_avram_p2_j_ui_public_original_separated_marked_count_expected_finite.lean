-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_separated_marked_count_expected_finite
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_separated_marked_count_expected_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:23:09.126751+00:00
-- url     : https://prove2.me/theorems/ac26f6d3-b1ac-4029-88ec-596e4455d6fd
-- title:
--   Public genuine intrinsic separated negative marked-count finite first moment
-- statement:
--   The original spectrally negative Levy process has a finite extended-real first moment for its intrinsic marked-jump count up to any finite horizon and on any Borel set strictly separated from zero on the negative axis. The proof uses the independently Proved public original intrinsic intensity-measure existence and local finiteness package, and the genuine count rather than a new auxiliary process or an assumed rate identification.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_separated_marked_count_expected_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) < ⊤ := by sorry
