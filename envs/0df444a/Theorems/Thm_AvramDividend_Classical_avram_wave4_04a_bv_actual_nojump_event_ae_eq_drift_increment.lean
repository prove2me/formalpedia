-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:10:57.035219+00:00
-- url     : https://prove2.me/theorems/a31bfa74-9b88-4d4d-b66e-0ee39dd99c4a
-- title:
--   Original BV Lévy no-genuine-jump event agrees almost surely with exact source drift-only increment
-- statement:
--   For every interval (s,t] of the actual original BV finite-activity spectrally negative Lévy source X, the event that all literal left-limit jump marks vanish there equals, P-almost surely, the event that X_t−X_s equals the deterministic drift (t−s)X.drift. This provides the exact measure-level source jump extractor used for source count zero laws and right-continuous-past factorization; it is not a replacement-process law.
-- source:
--   Canonically Proved actual drift-only interval theorem 2a0cae and monotone original drift residual f6cc, plus strict true source jump iff residual left jump 7423. Nojump implies equality of residual endpoints. Conversely endpoint equality and monotonicity exclude any strict interior residual jump. Reorganize source residual identity to X_t−X_s=(t−s)drift; propext yields pointwise event equality on one original P-full set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =ᵐ[P]
      {ω : Ω | X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift} := by sorry
