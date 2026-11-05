-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_grid_zero_mean
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_grid_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:56:01.765011+00:00
-- url     : https://prove2.me/theorems/2b55625c-513a-4d09-b1aa-53cdc2008cfc
-- title:
--   Original Lévy finite-grid adapted-compensated small-jump sum has zero mean
-- statement:
--   Actual intrinsic Lévy finite negative-mark-band counts on original Ω, multiplied by past-predictable source weights, have integrable finite compensated sum and zero mean. The exact original 𝓕_i rectangle P2-E first-moment law, physical count equality and L2 integrability of weights and counts are explicit source premises. This proves a finite-simple hZero bridge without assuming Poisson second moments, an auxiliary jump measure, filtration right-continuity, infinite activity convergence or stopping.
-- source:
--   Combines six Proved P4-G helpers, specifically b9aa20a2-c121-4b70-a9ac-be1148195789, with pinned Bochner integral_finset_sum and integrable_finset_sum.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_weighted_L2_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_grid_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hMeas : ∀ i, Measurable (N i))
    (hRect : ∀ (i : ℕ) (A : Set Ω),
      MeasurableSet[𝓕 (grid i)] A →
      (∫⁻ ω in A, N i ω ∂P) =
        P A * ((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (n : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
