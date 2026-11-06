-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:15:50.099268+00:00
-- url     : https://prove2.me/theorems/158e793f-6e18-4374-932e-8e1bf5e8fd2a
-- title:
--   Original finite-band signed jump integral equals a finite sum over actual source jump times
-- statement:
--   For every original spectrally negative Levy path and every canonical small-negative cutoff, construct the exact finite set of its own jump times in that band and identify the original signed intrinsic integral with the finite real sum of those exact X.X jumps. Finite support follows from the genuine original path jump support, with the quantitative one-over-(n+1) cutoff. No external Gaussian, auxiliary marked process or martingale premise.
-- source:
--   Proved P4-H original separated negative-band support d018dd24 and original signed source integral-to-jump-tsum 79505e86; only finite support and sum conversion.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∫ p in E, p.2 ∂N) = ∑ u ∈ F, j u := by sorry
