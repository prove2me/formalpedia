-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
-- name    : AvramDividend.Classical.avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:40:55.349174+00:00
-- url     : https://prove2.me/theorems/7a34a0dd-a03d-41b6-bbcb-62911634a8fa
-- title:
--   Nested clipped gradients agree outside two boundary strips and their difference is bounded
-- statement:
--   For two nested closed clipping bands, the piecewise gradient equals the derivative inside and one outside, so both clipped functions agree away from the two thin boundary strips. If the derivative is bounded on the larger band by a number at least one, the difference is bounded in absolute value by twice that number everywhere.
-- source:
--   Original finite-cap fixed-boundary B65 vs freely selected B220: deterministic cutoff perturbation lemma reduces L2 approximation differences to time occupation of shrinking boundary strips.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
    (w : ℝ → ℝ) (a a' b' b B : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (y : ℝ) :
    (y ∉ Set.Icc a a' → y ∉ Set.Icc b' b →
      (if y ∈ Set.Icc a b then deriv w y else 1) =
      (if y ∈ Set.Icc a' b' then deriv w y else 1)) ∧
    |(if y ∈ Set.Icc a b then deriv w y else 1) -
      (if y ∈ Set.Icc a' b' then deriv w y else 1)| ≤ 2 * B := by sorry
