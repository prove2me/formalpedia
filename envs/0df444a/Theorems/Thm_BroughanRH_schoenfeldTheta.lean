-- Prove2me | Theorems.Thm_BroughanRH_schoenfeldTheta
-- name    : BroughanRH.schoenfeldTheta
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:10:48.941581+00:00
-- url     : https://prove2.me/theorems/f2b6600e-0761-4812-9156-db6d1a46bf0f
-- title:
--   Schoenfeld’s explicit prime bound
-- statement:
--   The absolute Chebyshev error is strictly below $\sqrt{x}(\log x)^2/(8\pi)$ for all real $x\ge 599$. [Source](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.2. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem schoenfeldTheta :
    ∀ x : ℝ, (599 : ℝ) ≤ x → |Chebyshev.theta x - x| < Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) := by sorry

end BroughanRH
