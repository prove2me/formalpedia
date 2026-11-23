-- Prove2me | Theorems.Thm_BroughanRH_schoenfeldPrimeCounting
-- name    : BroughanRH.schoenfeldPrimeCounting
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:11:06.213863+00:00
-- url     : https://prove2.me/theorems/8ce1e1f0-3415-4131-bc6a-5a6ebb1ad7c5
-- title:
--   Schoenfeld’s explicit prime-counting bound
-- statement:
--   The prime-counting error against the principal-value logarithmic integral is strictly below $\sqrt{x}\log(x)/(8\pi)$ for $x\ge2657$. [Source](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.2. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem schoenfeldPrimeCounting :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    ∀ x : ℝ, 2657 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - li x| < Real.sqrt x * Real.log x / (8 * Real.pi) := by sorry

end BroughanRH
