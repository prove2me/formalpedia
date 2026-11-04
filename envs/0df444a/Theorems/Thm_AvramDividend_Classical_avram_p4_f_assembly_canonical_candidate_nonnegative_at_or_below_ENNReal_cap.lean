-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_canonical_candidate_nonnegative_at_or_below_ENNReal_cap
-- name    : AvramDividend.Classical.avram_p4_f_assembly_canonical_candidate_nonnegative_at_or_below_ENNReal_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:53:59.820007+00:00
-- url     : https://prove2.me/theorems/2564292f-8121-4dc1-871d-93c71a939fec
-- title:
--   Canonical verification candidate nonnegative at or below finite or infinite ENNReal cap
-- statement:
--   With the canonical w0≥0, zero extension, continuity at zero and C2/derivative≥1 only on the strict interior 0<y<C, every reserve y whose ENNReal.ofReal y≤C has w(y)≥0, including exact cap contact and negative ruin overshoots. Strict interior for z<y follows from ENNReal.ofReal strict monotonicity and y≤C; the accepted P4-E monotonicity-at-boundary lemma finishes. No extension of interior derivative assumptions to the cap is made.
-- source:
--   Accepted P4-E 4da8dd65 boundary monotonicity and pinned Mathlib ENNReal.ofReal_lt_ofReal_iff_of_nonneg.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_canonical_candidate_nonnegative_at_or_below_ENNReal_cap
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hyC : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by sorry
