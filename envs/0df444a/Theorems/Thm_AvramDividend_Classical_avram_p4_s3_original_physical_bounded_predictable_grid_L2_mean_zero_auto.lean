-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:55:36.355357+00:00
-- url     : https://prove2.me/theorems/57d3426f-c53f-4a59-9c4f-699db65f1858
-- title:
--   Physical bounded predictable negative-band finite-grid jump sum is square-integrable and mean zero
-- statement:
--   For physical marked jumps of the original spectrally negative Levy process, adapted square-integrable coefficients with a uniform pathwise bound on a bounded monotone time grid yield a compensated finite-band jump sum in L² and with exact zero expectation, automatically discharging original rate, count L² and rectangular compensation premises.
-- source:
--   Original-source P4-S3 physical finite-grid mean-zero fefe5cae and physical negative-Borel cell centred L² 963870c8, pinned Mathlib MemLp.of_bound, MemLp.mul, memLp_finset_sum.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
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
    (n : ℕ) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
