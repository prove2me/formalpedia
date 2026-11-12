-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_inclusive_frozen_A_step_integral
-- name    : AvramDividend.Classical.avram_bvb_b21_original_inclusive_frozen_A_step_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:04:45.796333+00:00
-- url     : https://prove2.me/theorems/cdc19ee6-a8c2-4017-b68a-218aa2a7aab8
-- title:
--   Original inclusive-cap negative-mark compensator grid equals its time-step integral
-- statement:
--   Exactly identifies the selected inclusive-cap original compensator quadrature A_n with a genuine time integral of its frozen left-endpoint kernel. It preserves weak reserve and top-cap inequalities, strict pre-ruin sampling, actual X, ν, D and Ω, and arbitrary nondecreasing physical grid intervals.
-- source:
--   Direct root-connected bridge to 7ccc2a1a original inclusive-cap K_n minus A_n convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_frozen_grid_sum_as_step_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_inclusive_frozen_A_step_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let c : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
        ∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν
      else 0
    (∑ i ∈ Finset.range (n + 1),
      c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
      ∫ t : ℝ, ∑ i ∈ Finset.range (n + 1),
        (Ico (u n i : ℝ) (u n (i + 1) : ℝ)).indicator
          (fun _ => c i) t := by sorry
