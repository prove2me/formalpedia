-- Prove2me | Theorems.Thm_Erdos68_factorial_tail_sharp_window
-- name    : Erdos68.factorial_tail_sharp_window
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-09T23:49:34.779831+00:00
-- url     : https://prove2.me/theorems/78fd65b0-0496-4d08-a0f4-e9ca4cb4dd53
-- title:
--   Erdős 68: sharp factorial tail window $M!\sum_{n>M}\frac1{n!-1}\in\bigl(\frac1{M+1},\frac1M\bigr)$
-- statement:
--   For every integer $M\ge 3$, the factorial-scaled tail of the Erdős 68 series
--   $$t_M\ :=\ M!\sum_{n=M+1}^{\infty}\frac{1}{n!-1}\ =\ M!\sum_{n=0}^{\infty}\frac{1}{(n+M+1)!-1}$$
--   lies in the open window
--   $$\frac{1}{M+1}\ <\ t_M\ <\ \frac{1}{M}\,.$$
--
--   This is the sharp analogue, at scale $M!$, of the platform lemma `Erdos68.factorial_series_tail_bound` ($0<\sum_{n\ge 0}\frac1{(n+N+2)!-1}<\frac{2}{(N+2)!}$), whose factor $2$ is too weak for window arguments: after multiplication by $M!$ it only yields $t_M<\frac{2}{M+1}$.
--
--   **The lemma is elementary.** The lower bound keeps the first term:
--   $$t_M>\frac{M!}{(M+1)!-1}>\frac{M!}{(M+1)!}=\frac1{M+1}\,.$$
--   For the upper bound, $\bigl((M+1)!-1\bigr)(M+2)^{n}\le (n+M+1)!-1$ for every $n\ge0$ (compare $(M+1)!\,(M+2)^n\le (n+M+1)!$), so comparison with the geometric series of ratio $1/(M+2)$ gives
--   $$\sum_{n\ge 0}\frac{1}{(n+M+1)!-1}\ \le\ \frac{1}{(M+1)!-1}\cdot\frac{M+2}{M+1},$$
--   hence
--   $$t_M\ \le\ \frac{M!}{(M+1)!-1}\cdot\frac{M+2}{M+1}\ <\ \frac1M\,,$$
--   where the last inequality rearranges to $M!>M+1$, valid for $M\ge 3$; this is exactly where the hypothesis $M\ge3$ is used (the statement remains true numerically at $M=2$, but $M\ge 3$ is the range needed downstream). The same computation appears in the accepted platform reduction of `Erdos68.irrational_from_tail_bounds` (submission `054f0b09-45e0-465c-9650-8d089f4cd21f`), lemmas `e68_tail_lower`, `e68_tail_upper`, `ht_lo`, `ht_hi`.
--
--   **Role in the decomposition.** This tail window converts the frontier leaf `Erdos68.factorial_moment_partial_sum_bound` (the fractional part of $A_M=\sum_{n=2}^M M!/(n!-1)$ avoids $\bigl(1-\frac1M,1-\frac1{M+1}\bigr)$) into the integer-separation statement `Erdos68.factorial_moment_integer_separation`, since $A_M + t_M = M!\,x$.
-- source:
--   Standard sharp tail estimate in the style of Fourier's proof of the irrationality of e. The identical computation appears in the accepted platform submission 054f0b09-45e0-465c-9650-8d089f4cd21f (reduction of Erdos68.irrational_from_tail_bounds), lemmas e68_tail_lower / e68_tail_upper / ht_lo / ht_hi; it sharpens the Proved node Erdos68.factorial_series_tail_bound (0 < R_N < 2/(N+2)!) to the exact window needed after scaling by M!.

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_tail_sharp_window (M : ℕ) (hM : 3 ≤ M) :
    1 / ((M : ℝ) + 1) < (M.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) ∧
    (M.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) < 1 / (M : ℝ) := by sorry

end Erdos68
