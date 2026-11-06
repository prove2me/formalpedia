-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:17:56.608938+00:00
-- url     : https://prove2.me/theorems/645e11c1-c4c8-4307-ad73-a0c211f86e69
-- title:
--   Original stopped finite negative-jump compensated grid jointly has L2 and mean zero
-- statement:
--   A finite right-continuously predictable, bounded, ruin-stopped compensated sum of the exact intrinsic physical negative Lévy jump counts belongs to L² and has expectation zero. Both components are certified by independent source-exact Proved theorems with their precise hypotheses; there is no conditional symbolic martingale axiom.
-- source:
--   Package Proved original process stopping-event L2 (b00789d9) and Proved original stop-time compensation/mean-zero (0091a275) into one source-exact ready-to-import pair.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_stopped_physical_grid_mean_zero_auto_count_L2
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_stopped_physical_grid_L2_mean_zero_joint
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
    (hν : ∀ i, X.ν (C i) < ⊤)
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
    let Z : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)
    MemLp Z 2 P ∧ (∫ ω, Z ω ∂P) = 0 := by sorry
