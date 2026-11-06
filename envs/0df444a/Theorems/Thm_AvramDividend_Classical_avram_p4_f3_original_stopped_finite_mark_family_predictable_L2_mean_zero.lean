-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:48:18.772545+00:00
-- url     : https://prove2.me/theorems/92f30741-c2a6-451d-b146-550735eeb891
-- title:
--   Original stopped predictable finite-mark compensated jump families are L2 and zero mean
-- statement:
--   On the original spectrally negative Lévy process X, its actual intrinsic negative-jump time-and-mark counts on a stopped time grid, multiplied by bounded coefficients measurable at each grid start, remain jointly square integrable and centred after summation over an arbitrary finite collection of mark cells. The construction uses the same Ω, P and right-continuous filtration and the original τ, with X.isProbability supplying the necessary probability instance. This is a genuine physical predictable stopped simple marked-jump martingale terminal for finite grids, and requires no new independent process. Infinite-mark and small-jump limits require separate L² convergence.
-- source:
--   Apply the remotely Proved P4-S3 physical-grid stopped negative band L2/mean-zero theorem 645e11c1 individually for each mark-cell index, then prove finite-sum MemLp by induction and finite-sum integral=0 via integrable and integral_finset_sum. This bridges one physical predictable mark band to genuinely marked finite simple integrands; no claimed infinite-activity or stochastic integral limit.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε)
    (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ j i, X.ν (C j i) < ⊤)
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (hHL2 : ∀ j i, MemLp (H j i) 2 P)
    (L : ι → ℝ) (hBound : ∀ j i ω, |H j i ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun j ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i ω) *
          ((N j i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C j i)).toReal)
    MemLp (fun ω => ∑ j ∈ F, Z j ω) 2 P ∧
      (∫ ω, ∑ j ∈ F, Z j ω ∂P) = 0 := by sorry
