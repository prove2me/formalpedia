-- Prove2me | Theorems.Thm_Erdos324_fourth_power_quadratic_perturbation_tail
-- name    : Erdos324.fourth_power_quadratic_perturbation_tail
-- status  : Proved
-- author  : @Mceppaglia
-- created : 2026-11-20T17:50:50.365875+00:00
-- url     : https://prove2.me/theorems/46859084-43bf-49ae-8031-cf56665d52f9
-- title:
--   Repeated pair sums in every tail of $n^4+c n^2$
-- statement:
--   Fix any integer $c$ and put $f_c(n)=n^4+c n^2$. For every natural number $N$ there are four pairwise distinct natural numbers $a,b,r,s$ above $N$, with $a<b$ and $r<s$, such that $f_c(a)+f_c(b)=f_c(r)+f_c(s)$. Thus every tail of this polynomial family has repeated pair sums. The general existence question of Erdős problem 324 remains open.
-- source:
--   Restricted case of Erdős and Graham, Old and New Problems and Results in Combinatorial Number Theory (1980), p. 53, https://www.erdosproblems.com/324. Matt selected this family and directed the investigation. OpenAI Codex developed the construction and Lean proof presented here. Browning, The polynomial sieve and equal sums of like polynomials, §3, (3.1), https://arxiv.org/abs/1306.6767, provides the underlying difference identity. Ulas, On certain diophantine equations related to triangular and tetrahedral numbers, Theorem 5.3, https://arxiv.org/abs/0811.2477, covers the coefficient -2 and hence its square multiples by dilation. The pure fourth-power identity is classical.

import Mathlib

theorem Erdos324.fourth_power_quadratic_perturbation_tail (c : ℤ) (N : ℕ) :
    ∃ a b r s : ℕ, N < a ∧ a < b ∧ N < r ∧ r < s ∧
      a ≠ r ∧ a ≠ s ∧ b ≠ r ∧ b ≠ s ∧
      (a : ℤ)^4 + c*(a : ℤ)^2 + ((b : ℤ)^4 + c*(b : ℤ)^2) =
      (r : ℤ)^4 + c*(r : ℤ)^2 + ((s : ℤ)^4 + c*(s : ℤ)^2) := by sorry
