-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
-- name    : AvramDividend.Classical.avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:27:15.15744+00:00
-- url     : https://prove2.me/theorems/d37d4343-76af-4bcd-a934-7bc509534d28
-- title:
--   Original compensated finite spatial-annulus sums belong to L2 and have zero mean
-- statement:
--   For the actual original Lévy jump measure on the original filtered probability space, every deterministic finite spatial partition sum of compensated physical negative-mark annulus counts belongs to L2(P) and has expectation zero. Obtain each band by specialising the Proved original-filtration bounded-predictable single-grid compensator result to the one-cell 0-to-T grid, then close the finite spatial sum under MemLp and integral linearity. This establishes centring needed for a genuine original-physical annulus L2 limit; it does not assert any stopped Ito-Meyer payoff bound.
-- source:
--   MIX-INFINITE19 root-connected original compensated annulus finite-family L2 centring prerequisite for the small-jump limit and 5f12c023 stopped mixed witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    ∀ k : ℕ,
      MemLp (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) = 0 := by sorry
