-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_derivative_eventually_left_increment
-- name    : AvramDividend.Classical.positive_derivative_eventually_left_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:20:36.490995+00:00
-- url     : https://prove2.me/theorems/95edcfcf-2984-42f3-87b8-0ad1b0583e38
-- title:
--   Positive derivative gives strict left scale increment near the barrier
-- statement:
--   If W has a strictly positive derivative at a, then W(a-epsilon) < W(a) for all sufficiently small positive epsilon. Reflect the graph horizontally and vertically, preserving the derivative, then invoke the already Proved right-increment theorem.
-- source:
--   Proved positive_derivative_eventually_right_increment (a7809b39-11ea-4c9b-9a76-425f4466d261) and Mathlib basic derivative chain and negation rules.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_positive_derivative_eventually_right_increment

open Filter Set
open scoped Topology

theorem AvramDividend.Classical.positive_derivative_eventually_left_increment
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W (a - ε) < W a := by sorry
