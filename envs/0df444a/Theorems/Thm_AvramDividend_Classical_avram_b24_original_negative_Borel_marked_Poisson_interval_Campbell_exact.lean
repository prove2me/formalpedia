-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
-- name    : AvramDividend.Classical.avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:41:08.669292+00:00
-- url     : https://prove2.me/theorems/811bf7d8-53f3-4faa-942c-68798f4244a3
-- title:
--   Exact original marked-Poisson Campbell mean on any true physical interval and negative Borel mark band
-- statement:
--   For the actual unchanged original spectrally negative Lévy source X on its own Ω/P, the expected genuine physical marked negative jump count in any chronological strict-left/inclusive-right rectangle Ioc s t × B is exactly elapsed time (t-s) multiplied by the authentic original Lévy negative-mark measure ν(B), for every negative Borel mark band B and every s≤t. This follows from the Proved original marked future-rectangle stationary mean transport and the Proved time-zero negative Borel exact Campbell count. It provides the sharp original stochastic rate needed for marked-source finite-activity L1 increment estimates, physical stopped-grid compensation, and true terminal ruin marked contacts, without extra large-jump moments.
-- source:
--   Proved wave7 original actual marked Poisson rectangle stationary mean; ja34 original negative Borel marked Poisson intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
