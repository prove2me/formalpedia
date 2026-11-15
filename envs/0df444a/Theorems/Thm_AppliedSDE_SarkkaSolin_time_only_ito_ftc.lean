-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_time_only_ito_ftc
-- name    : AppliedSDE.SarkkaSolin.time_only_ito_ftc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:59:35.971196+00:00
-- url     : https://prove2.me/theorems/6c497543-9cf4-43f0-a861-7f63dfc608e6
-- title:
--   C1 time-only Ito contribution as a Lebesgue integral on (0,T]
-- statement:
--   For a continuously differentiable deterministic time function f with continuous derivative ft and T>0, the time-only Ito contribution satisfies f(T)-f(0) = integral from 0 to T of ft(s) ds over (0,T]. This is the time component of the Chapter 4 time-dependent vector Ito formula and requires only C1 regularity in time.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 4; fundamental theorem of calculus.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.time_only_ito_ftc
    (f ft : ℝ → ℝ)
    (ht : ∀ s : ℝ, HasDerivAt f (ft s) s)
    (hftc : Continuous ft) (T : ℝ) (hT : 0 < T) :
    f T - f 0 =
      ∫ s in Set.Ioc (0 : ℝ) T, ft s ∂volume := by
  sorry
