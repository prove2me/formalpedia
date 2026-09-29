-- Prove2me | Theorems.Thm_Erdos68_factorial_moment_window_escape
-- name    : Erdos68.factorial_moment_window_escape
-- status  : Open
-- author  : @shivm
-- created : 2026-09-25T16:31:43.35679+00:00
-- url     : https://prove2.me/theorems/614ef215-6ae5-4128-af67-427dc65dc3d0
-- title:
--   Erdős 68: factorial moments escape the rationality window cofinally
-- statement:
--   For $M \ge 2$ let
--   $$A_M = \sum_{n=2}^{M} \frac{M!}{n!-1} \in \mathbb{Q}.$$
--   The claim is that for every $N$ there is $M \ge N$ such that the fractional part $\{A_M\}$ does **not** lie in the open interval $\left(1 - \tfrac{1}{M},\ 1 - \tfrac{1}{M+1}\right)$.
--
--   This is an exact discrete reformulation of the irrationality of $S = \sum_{n\ge 2} 1/(n!-1)$ (Erdős Problem 68). Write $M!\,S = A_M + t_M$ with $t_M = \sum_{m > M} M!/(m!-1)$; one has $1/(M+1) < t_M < 1/M$ for $M \ge 3$. If $S$ were rational, then $M!\,S \in \mathbb{Z}$ for all large $M$, forcing $\{A_M\} = 1 - t_M$ into the window for all large $M$. Conversely, if $\{A_M\}$ lies in the window for all large $M$, then $M!\,S$ is within $1/(M(M+1))$ of an integer for all large $M$; since this distance is multiplied by $M+1$ from $M$ to $M+1$, it must vanish, so $S$ is rational. Hence the statement is equivalent to $S \notin \mathbb{Q}$, phrased purely in terms of explicit rationals.
-- source:
--   Erdős Problem 68, https://www.erdosproblems.com/68 ; reformulation of the factorial-base criterion (cf. W. Cook, plectis-erdos, paper/68, factorial carry characterisation)

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_moment_window_escape :
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      Int.fract (∑ n ∈ Finset.range (M - 1),
          (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) ∉
        Set.Ioo (1 - 1 / (M : ℚ)) (1 - 1 / ((M : ℚ) + 1)) := by
  sorry

end Erdos68
