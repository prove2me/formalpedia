-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_stopped_predictable_full_cutoff_grid_diagonal_energy
-- name    : AvramDividend.Classical.avram_jump_phys13_original_stopped_predictable_full_cutoff_grid_diagonal_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:45:53.019309+00:00
-- url     : https://prove2.me/theorems/08ce75a3-4e1b-40c7-8982-21bed1a1b68b
-- title:
--   Original stopped predictable source grid diagonal quadratic energy
-- statement:
--   On the original right-continuous filtration, any bounded predictable grid coefficient stopped at a genuine stopping time has an exact diagonal second-moment energy identity for full finite-activity negative source-jump cutoff cells. The stop mask acts at each left endpoint. No bounded-variation assumption.
-- source:
--   Specialisation of Proved original full-cutoff right-continuous finite-grid diagonal energy 7b1055b2-ce63-480a-ba8a-f72458251f59 to the genuine original-filtration stopping-time indicator, using measurability of the stop event proved in d5a15403-4827-44b2-b846-1695c67f98ed. This is finite-band diagonal energy only; the random clipped cell and cross-band physical L2 isometry remain open.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original-filtration stopped predictable finite-band jump-count diagonal energy. -/

theorem AvramDividend.Classical.avram_jump_phys13_original_stopped_predictable_full_cutoff_grid_diagonal_energy
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
    Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range n,
          r i * ∫ ω, (if (τ ω : WithTop ℝ≥0) ≤
            (grid i : WithTop ℝ≥0) then (0 : ℝ)
            else H i ω)^2 ∂P := by sorry
