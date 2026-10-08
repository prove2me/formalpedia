-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_recursion_closed_form
-- name    : CorreaThreshold.Adaptive.recursion_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:47.03506+00:00
-- url     : https://prove2.me/theorems/da13dc59-c138-40e5-9846-f7c18f8db47b
-- title:
--   (9)–(10), p. 1463 — under (8) with x₀ = 1, x_{j+1}ⁿ⁻¹ = ((n − 1)/n)xⱼⁿ + x₁ⁿ⁻¹ − (n − 1)/n
-- statement:
--   Let $n\ge2$ and let $(x_i)_{i\ge0}$ be real numbers with $x_0=1$ satisfying
--   $$\frac{x_{i-1}^n}{n}-\frac{x_i^n}{n}=\frac{x_i^{n-1}}{n-1}-\frac{x_{i+1}^{n-1}}{n-1}\qquad(8)$$
--   for $i=1,\ldots,j$, where $j\ge1$. Then
--   $$x_{j+1}^{n-1}=\frac{n-1}{n}x_j^n+x_1^{n-1}-\frac{n-1}{n}.$$
--   With $\alpha_n=n-1-nx_1^{n-1}$ this is (9), $x_{j+1}=\big(\frac{n-1}{n}x_j^n-\frac{\alpha_n}{n}\big)^{1/(n-1)}$, raised to the power $n-1$; for $j=1$ it is (10).
--
--   It identifies the recursion with that of Hill and Kertz.
--
--   **Formalization Note** The statement is the $(n-1)$-st power of (9), so no real roots appear and it holds for all real $x_i$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1463, (9), (10) and the induction following (10)

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem recursion_closed_form {n : ℕ} (hn : 2 ≤ n) (x : ℕ → ℝ) (hx0 : x 0 = 1)
    (j : ℕ) (hj : 1 ≤ j)
    (h8 : ∀ i ∈ Finset.Icc 1 j,
        x (i - 1) ^ n / n - x i ^ n / n =
          x i ^ (n - 1) / ((n : ℝ) - 1) - x (i + 1) ^ (n - 1) / ((n : ℝ) - 1)) :
    x (j + 1) ^ (n - 1) = ((n : ℝ) - 1) / n * x j ^ n + x 1 ^ (n - 1) - ((n : ℝ) - 1) / n := by sorry

end CorreaThreshold.Adaptive
