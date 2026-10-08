-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_eq_46
-- name    : BnBPEP.WeakCvx.eq_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:06.995843+00:00
-- url     : https://prove2.me/theorems/f91acab7-17de-4bef-9cdd-13845f5d048c
-- title:
--   (46) — Bernoulli upper bound and a simpler majorant of (45)
-- statement:
--   Let $N\in\mathbb N$, $h\in(0,\tfrac12]$, $L>0$ and $\kappa\in\mathbb R$. Then
--
--   1. (Bernoulli's upper bound) $\displaystyle (1-2h)^{N+1}\le\frac{1}{2(N+1)h+1}$;
--   2. the right-hand side of (45) is bounded by the chain
--   $$\begin{aligned}
--   &\frac{L^2}{N+1}\Big[-1+(1-2h)^{N+1}+2h(N+1)+\kappa^2\frac{2}{h}\big(1-(1-2h)^{N+1}\big)\Big]\\
--   &\overset{a)}{<}\frac{L^2}{N+1}\Big[-1+\frac{1}{2(N+1)h+1}+2h(N+1)+\kappa^2\frac{2}{h}\Big]\\
--   &\overset{b)}{<}\frac{L^2}{N+1}\Big[-1+\frac{1}{2(N+1)h}+2h(N+1)+\kappa^2\frac{2}{h}\Big]\\
--   &=\frac{L^2}{N+1}\Big[-1+\frac{1}{2h}\Big(\frac{1}{N+1}+4\kappa^2\Big)+2h(N+1)\Big].
--   \end{aligned}\tag{46}$$
--
--   The last expression admits a closed-form minimizer in $h$, which yields the stepsize of Corollary 1.
--
--   **Formalization Note** All three relations of the chain are stated. Step a) is strict for every $h\in(0,\tfrac12]$ because the Bernoulli bound is strict for $h>0$; the paper's auxiliary remark $1-(1-2h)^{N+1}<1$ fails at $h=\tfrac12$, but the strict inequality a) still holds there. $L$ is the paper's $\widetilde L$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, p. 624, (46) and the Bernoulli bound below it

import Mathlib

namespace BnBPEP.WeakCvx

/-- (46), p. 624, with the Bernoulli bound used in step a): for `h ∈ (0, 1/2]`,
`(1 - 2h)^{N+1} ≤ 1/(2(N+1)h + 1)`, and the bracket of (45) is bounded by the chain
a) `<`, b) `<`, `=` ending in `(L²/(N+1)) [-1 + (1/(2h))(1/(N+1) + 4κ²) + 2h(N+1)]`. -/
theorem eq_46 (N : ℕ) (h L κ : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (hL : 0 < L) :
    (1 - 2 * h) ^ (N + 1) ≤ 1 / (2 * ((N : ℝ) + 1) * h + 1) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + (1 - 2 * h) ^ (N + 1) + 2 * h * ((N : ℝ) + 1)
          + κ ^ 2 * (2 / h) * (1 - (1 - 2 * h) ^ (N + 1)))
        < L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h + 1)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h)) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h + 1)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h))
        < L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h)) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h))
        = L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * h) * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * h * ((N : ℝ) + 1)) := by sorry

end BnBPEP.WeakCvx
