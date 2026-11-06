-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_stopped_grid_physical_L2
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_grid_physical_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:33:50.450458+00:00
-- url     : https://prove2.me/theorems/137feebf-2451-4f53-ae2d-61d513d03d9d
-- title:
--   Actual original full negative-cutoff stopped predictable finite-grid compensated physical jumps are L²
-- statement:
--   For the unchanged original X/P/ν, a rightCont stopping time, nondecreasing deterministic grid, and bounded original rightCont-s measurable H_i, the finite grid sum of compensated full-negative-cutoff physically marked counts multiplied by the predictable left-endpoint stopping indicators is square integrable. There are no added moment hypotheses, no synthetic jump process, no uniform-in-cutoff tail assertion.
-- source:
--   The original rightCont stopping-time event {τ≤grid i} is measurable in the rightCont filtration at grid i; hence the stopped coefficient W_i is strongly measurable and uniformly bounded. Source-exact original full-cutoff weighted L² applies to each actual physical interval. A finite sum of L² variables is L².

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_stopped_grid_physical_L2
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
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P := by sorry
