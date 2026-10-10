-- Prove2me | Theorems.Thm_Erdos68_factorial_moment_integer_separation
-- name    : Erdos68.factorial_moment_integer_separation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T23:49:35.049028+00:00
-- url     : https://prove2.me/theorems/31063e5a-0a1d-499f-a4ea-83a2a2c47202
-- title:
--   Erdős 68: factorial multiples of $\sum_{n\ge 2} 1/(n!-1)$ stay away from integers
-- statement:
--   Let
--   $$x=\sum_{n=2}^{\infty}\frac{1}{n!-1}=1.2216\ldots$$
--   be the Erdős 68 constant. The claim is that for every integer $M \ge 3$ and every integer $m$,
--   $$\bigl|\,M!\,x-m\,\bigr|\ \ge\ \frac{1}{M(M+1)}\,,$$
--   that is, the factorial multiple $M!\,x$ never comes within $1/(M(M+1))$ of an integer.
--
--   **Relation to Erdős Problem 68.** This separation property strictly strengthens the irrationality of $x$ asked by Erdős Problem 68 (https://www.erdosproblems.com/68, open): if $x=p/q$ were rational, then for every $M\ge q$ the number $M!\,x$ would be an integer, contradicting the displayed bound at $m=M!\,x$. Conversely, mere irrationality does not imply the quantitative bound, so this lemma is a genuinely stronger statement.
--
--   **Role in the decomposition.** This is the hard core of the frontier leaf `Erdos68.factorial_moment_partial_sum_bound` (window avoidance for the fractional part of $A_M=\sum_{n=2}^{M}M!/(n!-1)$). Writing $A_M+t_M=M!\,x$ with $t_M=M!\sum_{n>M}\frac1{n!-1}$, the companion lemma `Erdos68.factorial_tail_sharp_window` places $t_M$ in $\bigl(\frac1{M+1},\frac1M\bigr)$; if $\{A_M\}$ fell in the window $\bigl(1-\frac1M,\,1-\frac1{M+1}\bigr)$, then $\delta:=\lfloor A_M\rfloor+1-A_M$ would also lie in $\bigl(\frac1{M+1},\frac1M\bigr)$, and hence
--   $$\bigl|M!\,x-(\lfloor A_M\rfloor+1)\bigr|=|t_M-\delta|<\frac1{M(M+1)}\,,$$
--   contradicting the stated separation at $m=\lfloor A_M\rfloor+1$.
--
--   **Evidence.** Exact rational arithmetic for $A_M$ combined with 60-digit evaluation of the tail verifies the displayed bound for every $3\le M\le 299$ (and the window avoidance of the leaf over the same range); no counterexample is known, and no proof for general $M$ is known.
-- source:
--   Introduced for the Prove2me decomposition of `Erdos68.factorial_moment_partial_sum_bound` (mission 'Erdős Problem 68: Irrationality of sum 1/(n! - 1)'). Quantitative factorial-multiple form of Fourier's irrationality criterion applied to x = sum_{n>=2} 1/(n!-1); strictly strengthens the open Erdős Problem 68, https://www.erdosproblems.com/68. Verified numerically for all 3 <= M <= 299 by exact rational arithmetic for the partial sums and 60-digit tail evaluation.

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_moment_integer_separation (M : ℕ) (hM : 3 ≤ M) (m : ℤ) :
    1 / ((M : ℝ) * ((M : ℝ) + 1)) ≤
      |((M.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1))) - (m : ℝ)| := by sorry

end Erdos68
