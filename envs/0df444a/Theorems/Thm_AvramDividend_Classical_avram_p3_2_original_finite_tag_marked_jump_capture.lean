-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tag_marked_jump_capture
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_tag_marked_jump_capture
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:39:57.897208+00:00
-- url     : https://prove2.me/theorems/ce2efb92-e7ed-45a4-9e43-938ac7bae5d1
-- title:
--   Source-exact finite tagged original Lévy nonlinear jump capture
-- statement:
--   For any finite collection of genuine positive-time nonzero jumps of the original Lévy path and any measurable nonnegative nonlinear mark kernel F, the integral of F against the intrinsic original marked jump count, restricted by the finite jump-time tags, equals the finite sum of exactly those original marked jumps. Every tag is captured once with no independent mark process or finite activity assumption.
-- source:
--   The Proved original Lévy marked-count nonlinear integral-to-tsum theorem 008c9b37, finite-set measurable predicates and Mathlib tsum_eq_sum for finite support. This isolates the finite large-jump tags in the original physical grid limit route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- An arbitrary finite collection of genuine original Lévy marked times
is counted exactly once by the original marked counting integral. -/

theorem AvramDividend.Classical.avram_p3_2_original_finite_tag_marked_jump_capture
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,
      (if p.1 ∈ (T : Set ℝ≥0) then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ t ∈ T, F (t,
        X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) := by sorry
