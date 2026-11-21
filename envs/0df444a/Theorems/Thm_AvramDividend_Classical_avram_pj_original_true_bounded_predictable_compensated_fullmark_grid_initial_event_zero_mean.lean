-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_bounded_predictable_compensated_fullmark_grid_initial_event_zero_mean
-- name    : AvramDividend.Classical.avram_pj_original_true_bounded_predictable_compensated_fullmark_grid_initial_event_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:20:25.503902+00:00
-- url     : https://prove2.me/theorems/006efa02-3e1b-449e-9261-475d5b75d0d5
-- title:
--   True original bounded predictable stopped full negative-mark physical-grid martingale centred on arbitrary initial event
-- statement:
--   For the genuine original spectrally negative Lévy process and the exact physical negative-mark grid, finite horizon and true full cutoff, any uniformly bounded predictable square-integrable coefficient H has a centred compensated finite sum even when restricted to any event A measurable at every grid start, in particular any initial-filtration event. Apply the Proved original full-grid L2 mean-zero theorem 57d3426f to the true predictable coefficient masked by A; the original actual N increments and true compensators are unchanged. The resulting initial-event conditional centring is a necessary component in sound stopped Ito HJB verification and complements the unconditional Proved ff41c40e fullmark grid mean-zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_bounded_predictable_grid_L2_mean_zero_auto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_true_bounded_predictable_compensated_fullmark_grid_initial_event_zero_mean
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
    (n : ℕ)
    (A : Set Ω) (hSet : MeasurableSet A)
    (hSetAt : ∀ i, MeasurableSet[𝓕 (grid i)] A)
    (hL0 : 0 ≤ L) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) 2 P ∧
    (∫ ω in A, (∑ i ∈ Finset.range n, H i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
