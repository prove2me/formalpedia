-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_zero_count_event_ae_eq_drift_increment
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_zero_count_event_ae_eq_drift_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:10:35.976047+00:00
-- url     : https://prove2.me/theorems/d18331ab-ec17-4c7f-a040-165d727e95e0
-- title:
--   Actual intrinsic Lévy negative-jump count zero event equals the original drift-only increment event almost surely
-- statement:
--   For the actual original-space bounded-variation spectrally negative Lévy process with finite total negative jump intensity, the literal marked jump measure assigns zero mass to (s,t]×(-∞,0) precisely on an event P-a.e. equal to the original increment identity X_t−X_s=((t:ℝ)−(s:ℝ))*X.drift. This identifies the event of a genuine source-count void with a finite-dimensional source-X measurable increment event on the same filtration, a concrete bridge towards random-count measurability and grid-count Poisson laws. It is not an arbitrary count or compensator law.
-- source:
--   Canonically Proved all-sample source N_X zero iff genuine nojump event 4087af7c, and canonically Proved source BV nojump event =ᵐ[P] original drift increment event a31bfa74. Set.ext identifies the literal N_X count-zero event with genuine nojump, then a.e. equality transmits to X_t−X_s. No model replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_zero_count_event_ae_eq_drift_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} =ᵐ[P]
    {ω : Ω | X.X t ω - X.X s ω =
      ((t : ℝ) - (s : ℝ)) * X.drift} := by sorry
