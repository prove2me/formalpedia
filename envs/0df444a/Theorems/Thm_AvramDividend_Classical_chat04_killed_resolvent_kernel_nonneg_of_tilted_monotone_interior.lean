-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior
-- name    : AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:29:31.592129+00:00
-- url     : https://prove2.me/theorems/c769fe3c-469c-432a-aad6-1ee8a23df091
-- title:
--   Nonnegative killed-resolvent kernel from tilted scale monotonicity
-- statement:
--   For a nonnegative initial reserve x and spatial offset y between zero and x, monotonicity of the exponentially tilted scale function exp(-theta z)W(z) implies the killed-resolvent kernel exp(-theta y)W(x)-W(x-y) is nonnegative. This is the positivity property needed to treat the killed-resolvent kernel as a spatial potential density in Tonelli and positivity arguments.
-- source:
--   Direct algebraic consequence of monotonicity of exponentially tilted scale functions, as used in the spectrally negative Lévy scale-function resolvent density formula.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Set.Basic

open Real Set

theorem AvramDividend.Classical.chat04_killed_resolvent_kernel_nonneg_of_tilted_monotone_interior
    (θ : ℝ) (W : ℝ → ℝ)
    (hmono : MonotoneOn (fun z : ℝ => Real.exp (-(θ * z)) * W z) (Ici (0 : ℝ)))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    0 ≤ Real.exp (-(θ * y)) * W x - W (x - y) := by sorry
