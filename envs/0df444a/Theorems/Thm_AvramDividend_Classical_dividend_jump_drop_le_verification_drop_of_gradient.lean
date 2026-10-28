-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividend_jump_drop_le_verification_drop_of_gradient
-- name    : AvramDividend.Classical.dividend_jump_drop_le_verification_drop_of_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:37:00.7766+00:00
-- url     : https://prove2.me/theorems/2084a343-aeb9-4800-ba5d-ef26c81be7a8
-- title:
--   Dividend lump-sum secant inequality from marginal HJB gradient bound
-- statement:
--   Let a be the reserve immediately before a nonnegative lump-sum dividend d. Suppose w is continuous on the entire payment interval, differentiable on its interior, and its derivative is at least one there. The real mean-value theorem implies d ≤ w(a)-w(a-d). This is the lump-sum HJB gradient estimate used as the explicit jump-control hypothesis in the bounded- and unbounded-variation stochastic verification cores.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), dividend gradient inequality and verification.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Set
open AvramDividend.Classical

theorem AvramDividend.Classical.dividend_jump_drop_le_verification_drop_of_gradient
    (w : ℝ → ℝ) (a d : ℝ) (hd : 0 ≤ d)
    (hwCont : ContinuousOn w (Icc (a - d) a))
    (hwDiff : DifferentiableOn ℝ w (interior (Icc (a - d) a)))
    (hwGrad : ∀ y ∈ interior (Icc (a - d) a), 1 ≤ deriv w y) :
    d ≤ w a - w (a - d) := by sorry
