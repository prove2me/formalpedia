-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_physical_grid_L1_centered
-- name    : AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_physical_grid_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:13:41.931674+00:00
-- url     : https://prove2.me/theorems/424e687e-a679-44c7-ba6c-9e8e408e44bd
-- title:
--   Unbounded adapted original physical grid jump sum is integrable with zero mean
-- statement:
--   The finite original physical marked negative-Borel grid compensated sum with arbitrary strongly past-measurable L2 predictor H at every deterministic cell is integrable and has exactly zero expectation. All original count L2, rate finiteness and physical compensation obligations are discharged automatically by the true source lemmas, without requiring globally bounded H or an independent Poisson replacement.
-- source:
--   Assembles the proved P4-F3 original unbounded predictable source L1 mean zero 53e31b78 cell-by-cell with pinned Bochner integrable_finset_sum and integral_finset_sum. This yields finite-grid centred martingale support for the actual original Lévy path, leaving continuum L1/L2 convergence and stopped C2 Ito-Meyer separately.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_physical_grid_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i)
    let r : ℕ → ℝ := fun i =>
      ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
    Integrable (fun ω => ∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0 := by sorry
