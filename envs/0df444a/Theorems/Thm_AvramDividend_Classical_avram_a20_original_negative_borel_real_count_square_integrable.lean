-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_real_count_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T10:10:44.603355+00:00
-- url     : https://prove2.me/theorems/fe4e2905-9698-4f95-9045-3e77411af52c
-- title:
--   All original finite-activity negative Borel jump counts are genuinely square-integrable
-- statement:
--   In the original spectrally negative Lévy process, assume total negative-mark intensity finite. For any measurable Borel subset B of strictly negative marks and deterministic horizon T, the real-valued intrinsic count of actual jumps with marks in B has finite quadratic expectation. This is deduced by measurable domination by the all-negative count and the Proved original all-negative physical L2 bound. It removes the integrability component of the arbitrary-Borel factorial moment source obstruction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_real_count_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => ((N ω).toReal) ^ 2) P := by sorry
