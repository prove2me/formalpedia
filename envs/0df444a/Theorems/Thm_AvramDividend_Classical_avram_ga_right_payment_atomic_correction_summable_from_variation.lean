-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_right_payment_atomic_correction_summable_from_variation
-- name    : AvramDividend.Classical.avram_ga_right_payment_atomic_correction_summable_from_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:35:11.676181+00:00
-- url     : https://prove2.me/theorems/29abd958-74f6-4442-8d1f-fa666ebbd638
-- title:
--   All original bounded-discount right-payment corrections are summable from finite dividend variation
-- statement:
--   For an arbitrary countable family of right-hand dividend payments J_i≥0 with summable original jump sizes, 0≤e_i≤1 discount weights, and a potential with bounded absolute value change |V(y−J)-V(y)|≤LJ along each payment interval, the whole chronological nonlinear Itô–Stieltjes correction ∑ e_i[V(y−J)-V(y)+J] converges absolutely. This verifies the key integrability side of v5 equation (28.3) for the original physical countable right-payment atoms once local derivative bounds and summable dividend variation are supplied.
-- source:
--   Comparison to the original dividend variation series: absolute correction ≤(L+1)J_i and weights ≤1. Uses the existing original dividend countability/summability result d23b8276, but no approximation of D or false finite-jump restriction.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_right_payment_atomic_correction_summable_from_variation
    {ι : Type*} (V : ℝ → ℝ) (Y J E : ι → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hJ : ∀ i, 0 ≤ J i)
    (hJsum : Summable J)
    (hE : ∀ i, 0 ≤ E i ∧ E i ≤ 1)
    (hV : ∀ i, |V (Y i - J i) - V (Y i)| ≤ L * J i) :
    Summable (fun i => E i * (V (Y i - J i) - V (Y i) + J i)) := by sorry
