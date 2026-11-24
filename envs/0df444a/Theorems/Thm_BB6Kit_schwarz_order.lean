-- Prove2me | Theorems.Thm_BB6Kit_schwarz_order
-- name    : BB6Kit.schwarz_order
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T06:58:06.449234+00:00
-- url     : https://prove2.me/theorems/5c7ca722-84fd-4932-97b7-bd85ba1e14e3
-- title:
--   Schwarz lemma with a zero of order $J$: $|f(1)|\le\rho^{-J}\max_{|x|=\rho}|f(x)|$
-- statement:
--   **Lemma (Schwarz).** Let $f:\mathbb C\to\mathbb C$ be entire with $f^{(n)}(0)=0$ for all $n<J$, i.e. a zero of order at least $J$ at the origin. Let $\rho\ge1$ and suppose $|f(x)|\le B$ whenever $|x|=\rho$. Then $$|f(1)|\le\frac{B}{\rho^{J}}.$$
--
--   Proof idea: $g(x)=f(x)/x^J$ is entire, and on $|x|=\rho$ it satisfies $|g|\le B/\rho^J$. The maximum modulus principle gives the same bound at $x=1$, which lies in the closed disc since $\rho\ge1$. This is eq. (3.11) of the Mignotte–Voutier kit (Lemma 2.3, p. 37 of Waldschmidt's book).
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, eq. (3.11); M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups (Springer, 2000), Lemma 2.3 p. 37.

import Mathlib

namespace BB6Kit
theorem schwarz_order (f : ℂ → ℂ) (hf : Differentiable ℂ f) (J : ℕ)
    (hJ : ∀ n < J, iteratedDeriv n f 0 = 0) (ρ B : ℝ) (hρ : 1 ≤ ρ)
    (hB : ∀ x : ℂ, ‖x‖ = ρ → ‖f x‖ ≤ B) :
    ‖f 1‖ ≤ B / ρ ^ J := by
  sorry
end BB6Kit
