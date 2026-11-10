-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_zero_origin_centered_mean
-- name    : AvramDividend.Classical.avram_mix_annulus16_original_zero_origin_centered_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:48:03.677965+00:00
-- url     : https://prove2.me/theorems/6ddaed7b-c856-4724-a59d-d464275f577a
-- title:
--   Original negative-annulus physical count is centred at every deterministic horizon
-- statement:
--   The true compensated negative-annulus count over (0,T] has expected value zero on the original spectrally negative Lévy probability space. This follows directly by taking the one-cell constant predictable multiplier in the previously Proved original annulus finite-grid L2 centring theorem. It supplies the first moment for shifted conditional annulus isometry.
-- source:
--   Root-connected Proved 354411f0 original bounded predictable annulus count grid centring; feeds shifted annulus conditional first and second moments and ultimately 5f12c023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus16_original_zero_origin_centered_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (∫ ω, (N ω).toReal - r ∂P) = 0 := by sorry
