-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_lemma_7
-- name    : CorreaThreshold.Adaptive.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:42.323088+00:00
-- url     : https://prove2.me/theorems/4dd963d7-1562-452e-b4bf-d18f8f88d676
-- title:
--   Lemma 7, p. 1464 — for x₁ < (1 − β/n)^{1/(n−1)}, xᵢⁿ⁻¹ < y(i/n) for i = 1, …, n
-- statement:
--   Let $n\ge2$ and $\beta>1.25$, and let $y$ solve (ODE), $y'=y(\ln y-1)-(\beta-1)$, $y(0)=1$, on $[0,1]$ (continuous on $[0,1]$, with values in $(0,1]$ on $[0,1)$). Let $0\le x_1$ with $x_1^{n-1}<1-\beta/n$ (equivalently $x_1<(1-\beta/n)^{1/(n-1)}$), and let $x_2,x_3,\ldots$ follow the recursion (9), written for $w_i=x_i^{n-1}$ as $w_1=x_1^{n-1}$,
--   $$w_{i+1}=\frac{n-1}{n}\max(w_i,0)^{n/(n-1)}+x_1^{n-1}-\frac{n-1}{n}.$$
--   Then
--   $$x_i^{n-1}=w_i<y(i/n)\qquad(i=1,\ldots,n).$$
--
--   Choosing $\beta$ with $y(1)=0$ turns this into the bound $n(1-x_1^{n-1})\le\beta^*$.
--
--   **Formalization Note** The hypothesis $x_1<(1-\beta/n)^{1/(n-1)}$ is stated in the power form $x_1^{n-1}<1-\beta/n$, which is equivalent for $x_1\ge0$ and $\beta<n$, and is unsatisfiable (as it should be) when $\beta\ge n$. The recursion is carried by $w_i$; while $w_i\ge0$ it is exactly (9), and $\max(w_i,0)$ only matters after the recursion has turned negative, where $x_{i+1}$ is undefined on the page. $\beta>1.25$ is §4's standing assumption.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1464, Lemma 7; proof p. 1476

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem lemma_7 {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (hβ : 5 / 4 < β) (y : ℝ → ℝ)
    (hy : IsODESol β y 1) (x₁ : ℝ) (hx₁ : 0 ≤ x₁) (hx₁β : x₁ ^ (n - 1) < 1 - β / n) :
    ∀ i ∈ Finset.Icc 1 n, wseq n x₁ i < y ((i : ℝ) / n) := by sorry

end CorreaThreshold.Adaptive
