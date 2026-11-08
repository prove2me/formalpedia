-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
-- name    : AvramDividend.Classical.avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:04:57.554499+00:00
-- url     : https://prove2.me/theorems/fa593bb7-bea6-4dd8-a28e-3368c16e6b41
-- title:
--   Original stopped Lévy physical grid simultaneously localises reserve and measurable coefficients almost surely
-- statement:
--   For the exact original Lévy process, strategy, and physical grid, choose a cofinal reserve band and a deterministic bound for any measurable finite row coefficient array. For positive summable and vanishing tolerance bounds, there exist jointly measurable eventually exhausting sample events on which both the interior prepayment reserves and the coefficient array obey their row-specific cutoffs. Source exact, with no assumed L1 bounds or compensated-error convergence.
-- source:
--   Proved a32a3872 original measurable/eventual spatial masks, Proved 14a0bc0d rowwise coefficient cutoff in probability, and pinned Mathlib MeasureTheory.ae_finite_setOf_mem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_probability_diagonal
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (coeff : ℕ → Ω → ℕ → ℝ)
    (hcoeff : ∀ n i, Measurable (fun ω => coeff n ω i))
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ κ K : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, n ≤ κ n) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n ω, ω ∈ s n →
        (∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))) ∧
        (∀ i ∈ Finset.range (n + 1),
          abs (coeff n ω i) ≤ (K n : ℝ))) := by sorry
