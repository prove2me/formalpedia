-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_original_physical_negative_band_marked_laplace_collision
-- name    : AvramDividend.Classical.avram_redux18_original_physical_negative_band_marked_laplace_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:28:13.750322+00:00
-- url     : https://prove2.me/theorems/e7e02541-5355-424a-bdc1-46ca24c5373b
-- title:
--   Actual finite original negative-band jump marks have quadratic Laplace product remainder
-- statement:
--   For each actual spectrally negative Levy sample path, the set of physical marked jump times on any finite horizon whose negative marks lie in Iic(-1/(n+1)) is finite. The exponential of the sum of precisely those original left-limit jump marks differs from its first-order compensator by a nonnegative quantity at most half the original physical count's factorial pair count.
-- source:
--   Instantiate the Proved original finite marked negative-time set and its exact Set.ncard. Every selected mark is nonpositive because it lies below the negative cutoff. Apply the Proved local-negative-mark collision bound and use Set.ncard_eq_toFinset_card to identify the exact original physical count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_local_negative_mark_collision
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_original_physical_negative_band_marked_laplace_collision
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
        X ω T n).toFinset
    0 ≤ Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∧
    2 * (Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      (J.ncard : ℝ) * ((J.ncard : ℝ) - 1) := by sorry
