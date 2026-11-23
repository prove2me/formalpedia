-- Prove2me | Theorems.Thm_BroughanRH_habsieger
-- name    : BroughanRH.habsieger
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:29.88383+00:00
-- url     : https://prove2.me/theorems/a5dd21e3-1374-41cb-a6db-ac2f7d44ed99
-- title:
--   Habsieger’s fractional-part approximation to sine
-- statement:
--   Finite combinations of $\{nx\}-\{x\}$ approximate $\sin(2\pi x)/\pi$ in the square norm weighted by $dx/x^2$ on the positive ray.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem habsieger :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      let error (x : ℝ) := ((Real.sin (2*Real.pi*x)/Real.pi -
        ∑ j, a j * (Int.fract (((j.val+1 : ℕ):ℝ)*x) - Int.fract x))/x)^2
      MeasureTheory.IntegrableOn error (Set.Ioi 0) ∧
        (∫ x in Set.Ioi (0 : ℝ), error x) < ε := by sorry

end BroughanRH
