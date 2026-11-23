-- Prove2me | Theorems.Thm_BroughanRH_bagchiSequenceConstant
-- name    : BroughanRH.bagchiSequenceConstant
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:18.652059+00:00
-- url     : https://prove2.me/theorems/1b2c1e10-2952-44f8-b7bf-237dd2b71ad1
-- title:
--   Bagchi’s approximation of the constant sequence
-- statement:
--   The constant sequence belongs to the closed span of the fractional-part sequences in Bagchi’s Hilbert space with weight $1/(n(n+1))$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4 (Bagchi). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem bagchiSequenceConstant :
    let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
      ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
        ((n : ℝ)*(n+1))
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
      (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε := by sorry

end BroughanRH
