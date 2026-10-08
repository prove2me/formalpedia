-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_theorem_2_1_b
-- name    : AdaptiveCubic.Cauchy.theorem_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:30.686783+00:00
-- url     : https://prove2.me/theorems/3bafb06e-681e-4417-ac9b-5adb853c73ec
-- title:
--   Theorem 2.1 (2.14) — with $\sigma_k\ge\sigma_{\min}$, $|\mathcal U_j|\le\lceil(|\mathcal S_j|+1)\log(\bar\sigma/\sigma_{\min})/\log\gamma_1\rceil$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$. Fix $j\ge0$, let $\mathcal S_j$ and $\mathcal U_j$ be the successful and unsuccessful iterations among $0,\dots,j$, suppose that
--
--   $$\sigma_k\ge\sigma_{\min}\quad\text{for all }k\ge0 \qquad (2.11)$$
--
--   for some $\sigma_{\min}>0$, and let $\bar\sigma>0$ satisfy $\sigma_k\le\bar\sigma$ for all $k\le j+1$. Then
--
--   $$
--   |\mathcal U_j|\le\left\lceil\big(|\mathcal S_j|+1\big)\,\frac{1}{\log\gamma_1}\log\frac{\bar\sigma}{\sigma_{\min}}\right\rceil .
--   $$
--
--   This is the form of Theorem 2.1 used when the weights are bounded away from zero; no condition on very successful iterations is needed, because (2.11) and the upper bound imply $\sigma_{k+1}\ge(\sigma_{\min}/\bar\sigma)\sigma_k$.
--
--   **Formalization Note** As in (2.13), the bound $\sigma_k\le\bar\sigma$ is assumed for $k\le j+1$ instead of the printed $k\le j$; the printed version fails at $j=0$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 5, Theorem 2.1, (2.14)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Theorem 2.1, (2.14), p. 5 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
For any fixed `j ≥ 0`, with `S_j`, `U_j` as in (2.9): if `σ_k ≥ σ_min > 0` for all `k` (2.11) and
`σ_k ≤ σ̄`, then `|U_j| ≤ ⌈(|S_j| + 1) (1/log γ₁) log(σ̄/σ_min)⌉`. No (2.10) hypothesis is needed:
the page derives it from (2.11) with `γ₃ = σ_min/σ̄`.

Correction: (2.12) is assumed for `k ≤ j + 1` instead of the printed `k ≤ j` (see `theorem_2_1`). -/
theorem theorem_2_1_b {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (j : ℕ) (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈((((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℝ) + 1) *
        (1 / Real.log γ₁) * Real.log (σbar / σmin)⌉ := by sorry

end AdaptiveCubic.Cauchy
