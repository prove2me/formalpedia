-- Prove2me | Theorems.Thm_CappedBaseStock_two_branch
-- name    : CappedBaseStock.two_branch
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T01:48:32.973645+00:00
-- url     : https://prove2.me/theorems/5321ae50-81c5-4fb3-bc60-a282b7883482
-- title:
--   Proposition 4 — Comparison of the two cost bounds
-- statement:
--   Fix an integer $L\ge1$, put $\rho=L/(L+1)$ and $\kappa_L=1+4L^2/((L+1)(3L-1))$, and let $\lambda>0$ and $C_h,C_p\ge0$ be arbitrary real numbers. Then
--
--   $$\min\left\{(1+1/\lambda)C_h+(1+\rho)C_p,\ 2C_h+(1+\rho+\lambda\rho)C_p\right\}\le\kappa_L(C_h+C_p).$$
--
--   This purely algebraic statement includes the cases $C_h=0$ and $C_p=0$. There is no division by their sum and no positivity assumption on either component beyond nonnegativity. All divisions in the coefficients are real division; $L\ge1$ keeps their lead-time denominators positive.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines); public paper listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Author-supplied source SHA-256: f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Proposition 4 (`lem-two-branch`), lines 651–667.

import Mathlib

namespace CappedBaseStock


theorem two_branch
    (L : ℕ) (hL : 1 ≤ L)
    (lambda C_h C_p : ℝ)
    (hlambda : 0 < lambda) (hC_h : 0 ≤ C_h) (hC_p : 0 ≤ C_p) :
    min
      ((1 + 1 / lambda) * C_h + (1 + (L : ℝ) / ((L : ℝ) + 1)) * C_p)
      (2 * C_h +
        (1 + (L : ℝ) / ((L : ℝ) + 1) +
          lambda * ((L : ℝ) / ((L : ℝ) + 1))) * C_p) ≤
      (1 + 4 * (L : ℝ) ^ 2 / (((L : ℝ) + 1) * (3 * (L : ℝ) - 1))) *
        (C_h + C_p) := by sorry

end CappedBaseStock
