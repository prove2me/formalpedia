-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:44:37.106084+00:00
-- url     : https://prove2.me/theorems/d5a15403-4827-44b2-b846-1695c67f98ed
-- title:
--   Genuine original stopped full negative-cutoff predictable grid L² and exact zero terminal mean
-- statement:
--   For an actual rightCont-stopping time τ of original X and arbitrary bounded physical rightCont predictable grid coefficients H_i, the original marked negative-cutoff compensated counts on each deterministic grid cell, switched off at mesh starts after τ, have an L² finite-grid sum with exact zero mean. The stop is applied at predictable grid beginnings, so no unproved continuous-limit optional-stopping assertion.
-- source:
--   The rightCont stopping-time event {τ≤grid i} is rightCont-grid-i measurable. The stopped step coefficient W_i is strongly measurable and inherits the uniform bound. Apply the independent actual original full-cutoff finite-grid L²/zero-mean result to W.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_predictable_grid_L2_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
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
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
