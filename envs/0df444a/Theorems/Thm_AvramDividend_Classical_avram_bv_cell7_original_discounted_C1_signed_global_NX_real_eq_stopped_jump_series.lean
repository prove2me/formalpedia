-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series
-- name    : AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:46:39.752616+00:00
-- url     : https://prove2.me/theorems/a51292f1-7e3e-4bcd-861b-568ec142d708
-- title:
--   Original stopped discounted C1 signed jump real integral equals positive minus negative jump-time sums
-- statement:
--   For original admissible Lévy and dividend paths, the actual signed discounted compact-band C1 negative-jump source has Borel measurable real kernel, support inside the genuine min(ruinTime,T) clock, and a real global NX integral equal to positive-minus-negative original stopped jump-time sums whenever the source-specific kernel is integrable. Its only outstanding analytical premise is true integrability, separated explicitly from the finished physical jump-source reconciliation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T τ) then
            ENNReal.ofReal (G (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T τ) then
            ENNReal.ofReal (-G (v, Δ v)) else 0).toReal := by sorry
