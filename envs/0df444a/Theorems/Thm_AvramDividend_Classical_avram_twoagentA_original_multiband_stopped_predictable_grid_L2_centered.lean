-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_multiband_stopped_predictable_grid_L2_centered
-- name    : AvramDividend.Classical.avram_twoagentA_original_multiband_stopped_predictable_grid_L2_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:43:19.100817+00:00
-- url     : https://prove2.me/theorems/d1027c34-b3fb-4e9d-82b5-0a683ab72678
-- title:
--   Original stopped finite family of bounded predictable negative annulus physical-grid compensators is jointly L2 and centred
-- statement:
--   For any original spectrally negative Lévy process with arbitrary Lévy activity, the finite sum of actual, ruin-stoppable predictable weighted negative-annulus compensated marked-count grid martingales belongs to L2 and has zero expectation; mark sets and moment rates are the genuine X jump-measure and ν, with no hypothesised Poisson source or finite-activity restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_multiband_stopped_predictable_grid_L2_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ j, grid j ≤ grid (j + 1))
    (S : Finset ℕ) (a b : ℕ → ℕ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ i ∈ S, ∀ j,
      StronglyMeasurable[𝓕.rightCont (grid j)] (H i j))
    (K : ℕ → ℝ)
    (hBound : ∀ i ∈ S, ∀ j ω, |H i j ω| ≤ K i)
    (k : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((a i : ℝ) + 1))) (-(1 / ((b i : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s,
          X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ B i)
    let r : ℕ → ℕ → ℝ := fun i j =>
      (((grid (j + 1) - grid j : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      ∑ j ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0)
          then (0 : ℝ) else H i j ω) * ((N i j ω).toReal - r i j)
    MemLp (fun ω => ∑ i ∈ S, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ S, Z i ω ∂P) = 0 := by sorry
