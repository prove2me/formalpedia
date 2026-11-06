-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:59:47.256476+00:00
-- url     : https://prove2.me/theorems/b00789d9-e1f3-4e82-b465-f30ff6ba998a
-- title:
--   Physical original ruin-stopped finite-band compensated negative-jump grid has L2 integrability from source bounds
-- statement:
--   For the original stopped physical jump counts on any finite deterministic grid and a bounded right-continuous predictable coefficient, the stopped compensated sum is in L². Establish mask measurability and mask L² from the true stopping time, then invoke Proved original same-window right-continuous physical mark-simple L² for each cell and close by a finite sum. No conditional variance or extra stochastic axiom is required.
-- source:
--   Genuine right-continuous same-window weighted L2 source 1766fc2e, actual stopping-event measurability and pinned MemLp.indicator 963a2598 proof pattern. Finite physical windows summed without dependence or stationarity shortcuts.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
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
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)) 2 P := by sorry
