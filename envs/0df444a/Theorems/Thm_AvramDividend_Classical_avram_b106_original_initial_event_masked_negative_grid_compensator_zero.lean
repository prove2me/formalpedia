-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b106_original_initial_event_masked_negative_grid_compensator_zero
-- name    : AvramDividend.Classical.avram_b106_original_initial_event_masked_negative_grid_compensator_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:09:45.724003+00:00
-- url     : https://prove2.me/theorems/0747fa72-77d6-4915-ae03-506fc2e00a3c
-- title:
--   Original stopped negative-mark grid mean zero after masking by an initial-information event
-- statement:
--   For the original stopped finite-grid compensated negative Levy mark source, let bounded H be predictable at each actual grid left clock and A measurable in every grid left filtration. Mask the weight by A, preserving predictability and its absolute bound, and apply the Proved original finite-grid stopped compensated Poisson mark L2 zero-mean theorem. This establishes exactly zero expected original negative-mark source noise restricted to A. It uses no independent Gaussian process or global negative mark second moment.
-- source:
--   Original p4_s3_interval_h stopped finite-cutoff predictable negative mark L2 zero mean, Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A predictable initial event preserves exact original stopped finite-grid negative-cutoff centring. -/

theorem AvramDividend.Classical.avram_b106_original_initial_event_masked_negative_grid_compensator_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (A : Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] A)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, ∑ i ∈ Finset.range n,
      (if ω ∈ A then
         (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)
       else 0) * ((N i ω).toReal - r i) ∂P) = 0 := by sorry
