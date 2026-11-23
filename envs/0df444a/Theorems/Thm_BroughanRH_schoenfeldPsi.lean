-- Prove2me | Theorems.Thm_BroughanRH_schoenfeldPsi
-- name    : BroughanRH.schoenfeldPsi
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:09:10.461557+00:00
-- url     : https://prove2.me/theorems/336b159c-9ef0-413f-85d2-71398c16d297
-- title:
--   Schoenfeld’s explicit prime-power bound
-- statement:
--   The absolute Chebyshev error is strictly below $\sqrt{x}(\log x)^2/(8\pi)$ for all real $x\ge 73.2$. [Source](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.2. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem schoenfeldPsi :
    ∀ x : ℝ, (73.2 : ℝ) ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) := by sorry

end BroughanRH
