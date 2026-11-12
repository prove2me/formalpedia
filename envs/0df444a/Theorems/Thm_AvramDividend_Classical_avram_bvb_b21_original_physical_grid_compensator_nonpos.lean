-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_physical_grid_compensator_nonpos
-- name    : AvramDividend.Classical.avram_bvb_b21_original_physical_grid_compensator_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:35:41.110507+00:00
-- url     : https://prove2.me/theorems/d561659b-9036-4818-80e8-f4ddfddf5317
-- title:
--   Original stopped physical finite-grid marked compensator is nonpositive
-- statement:
--   The original left-limit pre-ruin finite-grid compensated negative-mark term J is nonpositive at every grid and path, since the negative-mark kernel has the Proved signed bound and each original grid interval has nonnegative length.
-- source:
--   Source-exact signed domination needed for original BV phys95, efbae9c3 and finite-activity mark-compensator reverse-Fatou step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_physical_grid_compensator_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
