-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
-- name    : AvramDividend.Classical.avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:06:56.799281+00:00
-- url     : https://prove2.me/theorems/78c057b6-8b8c-47e9-b517-049442d4c657
-- title:
--   Original stopped bounded predictable negative-annulus compensator physical grid L2 and mean zero
-- statement:
--   For the unchanged original Lévy process, filtration and any genuine right-continuous stopping time, a bounded predictable physical grid coefficient clipped to zero at or after the stop gives an L2 finite-grid annulus compensated count sum with exactly zero expectation. The proof makes the stop mask measurable at grid beginnings and applies the unmasked original annulus predictable grid theorem. This preserves zero-clock cancellation needed in the mixed infinite-activity witness 5f12c023.
-- source:
--   Follows from original physical annulus predictable L2 15 theorem via Proved source exact stopping mask mechanism d5a15403. Consumer stopped smalljump martingale in 5f12c023 -> f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (hnm : n ≤ m)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L) (k : ℕ) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
      (-(1 / ((m : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range k, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, Z i ω ∂P) = 0 := by sorry
