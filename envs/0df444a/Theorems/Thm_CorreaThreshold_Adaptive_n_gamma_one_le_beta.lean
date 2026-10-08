-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_n_gamma_one_le_beta
-- name    : CorreaThreshold.Adaptive.n_gamma_one_le_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:43.805357+00:00
-- url     : https://prove2.me/theorems/edf281ff-632e-476f-80b7-f280378721fe
-- title:
--   Proof of Theorem 2, pp. 1463–1465 — n(1 − x₁ⁿ⁻¹) ≤ β* for the solution of (8) with x₀ = 1, xₙ = 0
-- statement:
--   Let $n\ge2$ and let $\beta^*>1$ be the solution of (2), $\int_0^1dy/(y(1-\ln y)+(\beta^*-1))=1$. Let $x_0=1$, $x_n=0$, $x_1,\ldots,x_{n-1}>0$ satisfy
--   $$\frac{x_{i-1}^n}{n}-\frac{x_i^n}{n}=\frac{x_i^{n-1}}{n-1}-\frac{x_{i+1}^{n-1}}{n-1}\qquad(8)$$
--   for $i=1,\ldots,n-1$. Then
--   $$n\big(1-x_1^{n-1}\big)\le\beta^*.$$
--
--   Since $\gamma_1=1-x_1^{n-1}$, this bounds the factor $n\gamma_1$ of Lemma 5; it is also the bound $a_n\le\beta^*$ for the Hill–Kertz constants $a_n=n(1-x_1^{n-1})$.
--
--   **Formalization Note** $\beta^*$ enters through its defining equation (2) and $\beta^*>1$, so the statement is about the paper's constant (see the uniqueness milestone). Positivity of $x_1,\ldots,x_{n-1}$ is the paper's $x_i=1-\varepsilon_i$ with $\varepsilon_i<1$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), pp. 1463–1465, proof of Theorem 2 (‘It remains to show that n(1 − x₁^{n−1}) ≤ β*’) and §4 ‘Bounding γ₁’

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem n_gamma_one_le_beta {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (hβ1 : 1 < β)
    (hβ : ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (β - 1)) = 1)
    (x : ℕ → ℝ) (hx0 : x 0 = 1) (hxn : x n = 0) (hxpos : ∀ i ∈ Finset.Icc 1 (n - 1), 0 < x i)
    (h8 : ∀ i ∈ Finset.Icc 1 (n - 1),
        x (i - 1) ^ n / n - x i ^ n / n =
          x i ^ (n - 1) / ((n : ℝ) - 1) - x (i + 1) ^ (n - 1) / ((n : ℝ) - 1)) :
    (n : ℝ) * (1 - x 1 ^ (n - 1)) ≤ β := by sorry

end CorreaThreshold.Adaptive
