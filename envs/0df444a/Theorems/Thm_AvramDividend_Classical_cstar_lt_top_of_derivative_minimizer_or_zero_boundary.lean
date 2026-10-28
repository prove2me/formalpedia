-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_derivative_minimizer_or_zero_boundary
-- name    : AvramDividend.Classical.cstar_lt_top_of_derivative_minimizer_or_zero_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:14:26.956006+00:00
-- url     : https://prove2.me/theorems/9f3e10de-7b56-42f2-a2a4-2da79964d9a7
-- title:
--   Finite Avram dividend barrier from a positive derivative minimiser or zero-boundary lower derivative
-- statement:
--   The exact derivative dichotomy says that either the positive derivative admits a global minimiser or its extended right-hand zero derivative is a lower bound everywhere on the positive half-line. The already Proved theorem cstar_lt_top_iff_minimizer_or_zero_boundary identifies this disjunction with finiteness of the Avram barrier. Expanding cstarSet identifies the existential minimiser hypothesis with its nonemptiness. This is the elementary analytic implication needed to assemble the canonical finiteness theorem after the difficult scale-derivative dichotomy is established.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5, Lemma 2(i), zero-barrier and derivative-minimiser dichotomy.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary

open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_lt_top_of_derivative_minimizer_or_zero_boundary
    (W : ℝ → ℝ)
    (hcases : (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)) :
    cstar W < ⊤ := by sorry

end AvramDividend.Classical
