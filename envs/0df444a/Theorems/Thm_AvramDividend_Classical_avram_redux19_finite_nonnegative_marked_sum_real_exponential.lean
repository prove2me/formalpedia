-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_finite_nonnegative_marked_sum_real_exponential
-- name    : AvramDividend.Classical.avram_redux19_finite_nonnegative_marked_sum_real_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:42:48.842315+00:00
-- url     : https://prove2.me/theorems/2d3cde50-f679-477e-9661-3c100a24f67c
-- title:
--   Finite ENNReal mark magnitude integral converts to a real exponential
-- statement:
--   The exponential of the negative finite ENNReal mark-magnitude integral agrees exactly with the exponential of the signed real finite mark sum. The equality is used to connect the original strict-cutoff intrinsic jump integral to its physical finite jump product, with every mark nonnegative after reversing the sign.
-- source:
--   Use the pinned exact ENNReal.toReal_sum, ENNReal.toReal_ofReal and ENNReal.ofReal_ne_top theorems, followed by the finite sum negation identity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_finite_nonnegative_marked_sum_real_exponential
    {α : Type*} (S : Finset α) (a : α → ℝ)
    (ha : ∀ u ∈ S, 0 ≤ a u) :
    Real.exp (-(∑ u ∈ S, ENNReal.ofReal (a u)).toReal) =
      Real.exp (∑ u ∈ S, -a u) := by sorry
