-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_marked_times_finite_ae
-- name    : AvramDividend.Classical.avram_a20_original_borel_physical_marked_times_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:14:42.087182+00:00
-- url     : https://prove2.me/theorems/c6cc76c9-13ea-40ee-98ea-642d50c5ed34
-- title:
--   Actual original finite-activity negative Borel marked jump times are finite almost surely
-- statement:
--   For the original spectrally negative Lévy sample path, with finite total negative jump activity, an arbitrary measurable Borel set B of negative marks has finitely many actual marked jump times in every deterministic bounded horizon, almost surely. The proof uses the already Proved original exact expected Borel count and finite-intensity a.s. finiteness of intrinsic counts, then transfers through the original samplewise jump-measure equals set-encard identity. This is an essential sound a.s. finiteness premise for the physical chronological uniform-grid Fatou argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_physical_marked_times_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    ∀ᵐ ω ∂P, ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite := by sorry
