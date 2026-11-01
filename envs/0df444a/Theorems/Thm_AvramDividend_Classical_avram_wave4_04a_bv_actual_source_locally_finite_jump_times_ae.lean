-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:49:17.670819+00:00
-- url     : https://prove2.me/theorems/e35efd8b-dffe-441a-8742-4aedd214f484
-- title:
--   One full-measure event makes the genuine original finite-activity BV Lévy jump-time support locally finite on every horizon
-- statement:
--   For a genuine original spectrally negative Lévy source X with bounded variation and finite negative Lévy intensity, there is a single event of P-probability one on which the actual set of strictly positive nonzero X-jump times is finite on [0,T] for every real nonnegative T simultaneously. This follows from countable intersection of integer-horizon almost-sure finite-source-jump properties and Archimedean domination. No reference to an auxiliary Lévy process or a substituted filtration is made.
-- source:
--   The original-space finite-horizon source-X jump theorem avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon (publishing and proof pending) supplies each integer horizon. Mathlib MeasureTheory.ae_all_iff forms one P-full event for all natural horizons; Archimedean exists_nat_gt bounds each real T by a larger integer. Finiteness is inherited by subsets.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by sorry
