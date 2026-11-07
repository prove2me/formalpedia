-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_laplace_collision
-- name    : AvramDividend.Classical.avram_redux19_original_strict_negative_marked_laplace_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:31:08.989608+00:00
-- url     : https://prove2.me/theorems/9cf0f7c2-4b23-40f2-bb95-b1fd901463d9
-- title:
--   Original strict negative-band finite marked Laplace product has quadratic collision remainder
-- statement:
--   For every original Lévy sample path and exact strict negative cutoff of the intrinsic marked Laplace theorem, the physical finite marked-jump product has a nonnegative second-order error bounded by the strict physical jump-count factorial pair number. Zero time and the final horizon are handled with the same original interval conventions.
-- source:
--   Use the Proved strict original finite marked-time theorem to construct the actual strict-time Finset, prove selected marks are nonpositive, instantiate Proved local-negative-mark collision and rewrite the Finset cardinal as the original strict jump-time Set.ncard.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux18_local_negative_mark_collision
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_strict_negative_marked_laplace_collision
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
        X ω T k).toFinset
    0 ≤ Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∧
    2 * (Real.exp (∑ u ∈ S,
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
      (1 - ∑ u ∈ S,
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      (J.ncard : ℝ) * ((J.ncard : ℝ) - 1) := by sorry
