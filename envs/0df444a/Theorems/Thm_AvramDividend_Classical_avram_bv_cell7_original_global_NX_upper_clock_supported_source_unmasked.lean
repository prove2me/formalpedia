-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
-- name    : AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:25:59.669054+00:00
-- url     : https://prove2.me/theorems/c7b4bcaa-5d30-4697-942c-9c58a864e792
-- title:
--   Original global Lévy jump source can remove the upper-clock indicator when supported
-- statement:
--   On the genuine original global Lévy marked jump measure, any measurable nonnegative marked source vanishing beyond a fixed positive clock has exactly the same global integral before and after restriction to the original half-open interval from zero through that clock. This follows directly from the actual global count-to-tsum theorem, including the origin jump exclusion; the original C1 support child will discharge its only source-specific condition.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (hSupport : ∀ p : ℝ≥0 × ℝ, s < p.1 → F p = 0) :
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    (∫⁻ p, F p ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then F p else 0) ∂NX) := by sorry
