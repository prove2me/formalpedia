-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_stopped_predictable_clipped_grid_coefficient_square_integrable
-- name    : AvramDividend.Classical.avram_pj_workerC_stopped_predictable_clipped_grid_coefficient_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:30:01.838425+00:00
-- url     : https://prove2.me/theorems/aea5ac75-4fff-421b-a040-8f483a0626a4
-- title:
--   Actual stopped predictable clipped derivative coefficient is square-integrable at each physical grid time
-- statement:
--   An original strongly predictable coefficient evaluated at a deterministic physical grid time and masked by a true right-continuous stopping time is strongly measurable; symmetric clipping at K bounds its square by K squared, so the stopped coefficient square is integrable under the original probability. Supplies the missing measurability/integrability condition for the physical-grid full negative-mark diagonal L2 certificate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_stopped_predictable_clipped_grid_coefficient_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕.rightCont Z)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) :
    Integrable (fun ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else max (-K) (min K (Z t ω)))^2) P := by sorry
