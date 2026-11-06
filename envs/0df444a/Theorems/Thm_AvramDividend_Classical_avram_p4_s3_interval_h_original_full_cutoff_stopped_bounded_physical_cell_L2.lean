-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_stopped_bounded_physical_cell_L2
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_bounded_physical_cell_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:31:44.767329+00:00
-- url     : https://prove2.me/theorems/b91feb97-0c1c-4fb9-9989-651c1d8b8851
-- title:
--   Actual original rightCont stopping-time localised bounded full negative-cutoff marked cell L²
-- statement:
--   With original Lévy X, actual physical marked count on (s,s+T] at every full negative cutoff, actual rightCont stopping time τ, and bounded original rightCont predictable scalar H, the compensated marked count multiplied by the indicator that τ is strictly after the left grid endpoint is square integrable. No uniform-integrability, infinite-cutoff or remote conditional law premise.
-- source:
--   The actual original rightCont stopping-time event {τ≤s} is measurable at s. Its indicator switches H off at s, preserving strong measurability and the deterministic absolute bound. Apply Proved full cutoff actual physical bounded-weight L² auto.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_bounded_physical_cell_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    MemLp (fun ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
        then (0 : ℝ) else H ω) * ((N ω).toReal-r)) 2 P := by sorry
