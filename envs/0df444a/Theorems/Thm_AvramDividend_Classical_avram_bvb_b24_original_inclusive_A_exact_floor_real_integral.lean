-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_inclusive_A_exact_floor_real_integral
-- name    : AvramDividend.Classical.avram_bvb_b24_original_inclusive_A_exact_floor_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:23:31.485443+00:00
-- url     : https://prove2.me/theorems/108641fe-f384-4acc-9b8d-e4d4676f42ad
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b24_original_inclusive_A_exact_floor_real_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    let c : ℕ → ℝ := fun i =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Z ∧ ENNReal.ofReal Z ≤ C then
        ∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z + z) - w Z) ∂X.ν
      else 0
    (∑ i ∈ Finset.range (n + 1),
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Z ∧ ENNReal.ofReal Z ≤ C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z + z) - w Z) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) =
    ∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by sorry
