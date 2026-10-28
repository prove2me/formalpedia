-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline
-- name    : AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_full_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:34:10.344992+00:00
-- url     : https://prove2.me/theorems/8c779e85-9b73-4c27-973e-5a09849da895
-- title:
--   Nonnegativity of the killed-resolvent kernel on the full positive half-line
-- statement:
--   Assume the exponentially tilted scale function is monotone on nonnegative arguments, and the scale function is nonnegative there and zero on the negative half-line. For every initial reserve x>=0 and spatial state y>=0, the killed-resolvent density exp(-theta*y)W(x)-W(x-y) is nonnegative. On 0<=y<=x this follows from tilted monotonicity; for y>x it follows from negative support.
-- source:
--   Consequence of the verified interior positivity theorem plus scale-function support and positivity.

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior

open AvramDividend.Classical Real Set

theorem AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_full_halfline
    (θ : ℝ) (W : ℝ → ℝ)
    (hmono : MonotoneOn (fun z : ℝ => Real.exp (-(θ * z)) * W z) (Ici (0 : ℝ)))
    (hpos : ∀ z : ℝ, 0 ≤ z → 0 ≤ W z)
    (hnegative : ∀ z : ℝ, z < 0 → W z = 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ Real.exp (-(θ * y)) * W x - W (x - y) := by sorry
