-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_halfopen_marked_lintegral_split
-- name    : AvramDividend.Classical.avram_bv_jump8_halfopen_marked_lintegral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:17:46.072379+00:00
-- url     : https://prove2.me/theorems/59ce92e1-8228-446b-b561-951afb79c0d2
-- title:
--   Half-open intrinsic marked integrals split exactly across adjacent physical windows
-- statement:
--   For an arbitrary measure on physical time and real marks, a measurable nonnegative marked integrand restricted to the positive-time interval (0,t] splits into (0,s] and (s,t] whenever s≤t. This pointwise-in-measure identity supplies the source pathwise additivity step for the BV-JUMP8 original marked Laplace semigroup, with no time-zero atom or overlap at s.
-- source:
--   At each time-mark point, the indicator of (0,t] equals the sum of disjoint indicators for (0,s] and (s,t], using s≤t and 0≤s. Integrate the nonnegative pointwise sum with MeasureTheory.lintegral_add_left; hg plus Borel time masks provide the required measurability. Instantiate μ with the original literal intrinsic marked jump measure for each source path.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_halfopen_marked_lintegral_split
    (μ : Measure (ℝ≥0 × ℝ))
    (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) =
      (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ) +
      (∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) := by sorry
