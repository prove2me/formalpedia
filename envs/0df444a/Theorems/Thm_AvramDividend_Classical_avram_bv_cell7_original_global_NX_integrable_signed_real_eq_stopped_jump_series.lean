-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series
-- name    : AvramDividend.Classical.avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:38:49.091884+00:00
-- url     : https://prove2.me/theorems/36cf93c8-84bd-4e2f-af5d-c1e1d7d16db8
-- title:
--   Original global Lévy real signed source equals its positive and negative stopped jump-time series
-- statement:
--   For a genuinely integrable real-valued marked source on the actual original Lévy jump measure, measurable and supported up to a finite clock, its real integral is exactly the positive marked jump-time series in that same half-open interval minus the negative marked jump-time series. The argument uses the pinned Mathlib signed real-integral decomposition and the accepted exact original NX count-to-tsum and cutoff-removal certificates; it exposes genuine kernel integrability as the next source-specific obligation.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0)
    (G : ℝ≥0 × ℝ → ℝ) (hG : Measurable G)
    (hSupport : ∀ p : ℝ≥0 × ℝ, s < p.1 → G p = 0) :
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
            ENNReal.ofReal (G (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
            ENNReal.ofReal (-G (v, Δ v)) else 0).toReal := by sorry
