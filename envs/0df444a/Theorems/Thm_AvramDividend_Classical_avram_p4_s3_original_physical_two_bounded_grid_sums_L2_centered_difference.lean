-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_two_bounded_grid_sums_L2_centered_difference
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_two_bounded_grid_sums_L2_centered_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:11:12.481612+00:00
-- url     : https://prove2.me/theorems/daf79764-0bb7-43b0-b3d2-b709379120f1
-- title:
--   Any two original bounded predictable negative-band finite-grid compensated sums have L² mean-zero difference
-- statement:
--   For genuine physical marked negative-band jumps of a spectrally negative Levy process, any two finite prefixes of a bounded monotone predictable-grid compensated count sum have square-integrable difference with exact zero expectation. The proof uses verified physical finite-grid martingale centring and the new bounded-predictable L² source adapter. This supplies an L² increment interface for approximation, with no asserted tail convergence.
-- source:
--   P4-S3 source original finite-grid mean-zero fefe5cae and source bounded predictable grid L² helper 57d3426f, Mathlib MemLp.sub and integral_sub.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_two_bounded_grid_sums_L2_centered_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : ∀ i ω, |H i ω| ≤ L)
    (m n : ℕ) :
    let S : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ Finset.range k, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)
    MemLp (fun ω => S n ω - S m ω) 2 P ∧
    (∫ ω, S n ω - S m ω ∂P) = 0 := by sorry
