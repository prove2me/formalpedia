-- Prove2me | Theorems.Thm_DetDLP_terminal_digit_query_size_and_count
-- name    : DetDLP.terminal_digit_query_size_and_count
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T19:40:44.63879+00:00
-- url     : https://prove2.me/theorems/d8e6b4c8-6231-4166-9ad7-57e94abccf8f
-- title:
--   Linear sizes and subexponential count for terminal scalar digit queries
-- statement:
--   For every residual vertex count permitted by the terminal expansion, the actual digit-query precision and truncation length are positive and at most a fixed constant times the original bit parameter. The vertex count is polynomial in that parameter. Even at the full precision including the guard, the number of simultaneous digit choices is at most the exponential of a constant times the thirteen-tenths power of the logarithm of the core size. All constants are uniform over the instances.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.3, proof of Theorem 4.3, size and number of the scalar digit queries.

import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

theorem terminal_digit_query_size_and_count (C : ℕ) : ∃ (K e : ℕ) (c : ℝ),0 ≤ c ∧
    ∀ (S m b p ell edges n : ℕ),let L := Nat.clog 2 S
      let D := Nat.clog 32 (4*m)
      let q := p+64*(S+1)*(L+1)*2^L*64^D
      let h := max 1 (edges/(n+1))
      24+2*C ≤ L → 2 ≤ b → 0 < m → 0 < ell → 2 ≤ S → 4*m ≤ 2*S → b ≤ 2*C*S →
      m ≤ C*blockCount b → S ≤ C*m*b → edges ≤ C*b → ell ≤ C*m → p ≤ S →
      n ≤ 4*m+64^D →
      1 ≤ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ∧ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ≤ K*b ∧
      1 ≤ (n*(4*L-1)+1)*ell ∧ (n*(4*L-1)+1)*ell ≤ K*b ∧ n ≤ b^e ∧
      (((q/h+1)^n:ℕ):ℝ) ≤ Real.exp (c*(L:ℝ)^(13/10:ℝ)) := by sorry

end DetDLP
