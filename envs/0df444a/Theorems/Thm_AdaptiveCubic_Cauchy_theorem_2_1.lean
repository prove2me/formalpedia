-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_theorem_2_1
-- name    : AdaptiveCubic.Cauchy.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:40.283148+00:00
-- url     : https://prove2.me/theorems/4f230391-1f25-49b0-902b-419cd979a781
-- title:
--   Theorem 2.1 (2.13) — unsuccessful iterations are bounded by successful ones and $\log(\bar\sigma/\sigma_0)$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$. Fix $j\ge0$ and let $\mathcal S_j$ and $\mathcal U_j$ be the successful and unsuccessful iterations among $0,\dots,j$. Assume that for some $\gamma_3\in(0,1]$, every very successful iteration $k\le j$ has
--
--   $$\sigma_{k+1}\ge\gamma_3\sigma_k \qquad (2.10)$$
--
--   and let $\bar\sigma>0$ satisfy $\sigma_k\le\bar\sigma$ for all $k\le j+1$. Then
--
--   $$
--   |\mathcal U_j|\le\left\lceil-\frac{\log\gamma_3}{\log\gamma_1}\,|\mathcal S_j|+\frac{1}{\log\gamma_1}\log\frac{\bar\sigma}{\sigma_0}\right\rceil .
--   $$
--
--   Every unsuccessful iteration multiplies $\sigma$ by at least $\gamma_1>1$ and every successful one by at least $\gamma_3$, so an upper bound on $\sigma$ caps the number of unsuccessful iterations. This is the step that converts a count of successful iterations into a count of all iterations.
--
--   **Formalization Note** The paper assumes (2.12), $\sigma_k\le\bar\sigma$, only for $k\le j$. Its proof bounds $\sigma_{j+1}$ (the factor of iteration $j$ acts on $\sigma_{j+1}$), and as printed the statement fails for $j=0$ with iteration $0$ unsuccessful and $\bar\sigma=\sigma_0$ ($|\mathcal U_0|=1>\lceil0\rceil$). The hypothesis is therefore taken for $k\le j+1$; every application in the paper supplies this.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 5, Theorem 2.1, (2.13)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Theorem 2.1, (2.13), p. 5 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
For any fixed `j ≥ 0`, with `S_j` the successful and `U_j` the unsuccessful iterations `k ≤ j`
(2.9), assume (2.10) (`σ_{k+1} ≥ γ₃ σ_k` on every very successful `k ≤ j`, `γ₃ ∈ (0, 1]`) and let
`σ̄ > 0` bound `σ_k`. Then `|U_j| ≤ ⌈−(log γ₃ / log γ₁)|S_j| + (1/log γ₁) log(σ̄/σ₀)⌉`.

Correction: the page assumes (2.12) `σ_k ≤ σ̄` only for `k ≤ j`; the proof uses `σ_{j+1} ≤ σ̄`
((2.15) bounds `σ_{j+1}`), and the printed statement fails for `j = 0`, iteration `0` unsuccessful,
`σ̄ = σ₀`. The hypothesis is posed for `k ≤ j + 1`. -/
theorem theorem_2_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (j : ℕ) (γ₃ : ℝ) (hγ₃ : 0 < γ₃) (hγ₃' : γ₃ ≤ 1)
    (h210 : ∀ k ≤ j, η₂ < rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1))
    (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈-(Real.log γ₃ / Real.log γ₁) *
          (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℝ) +
        1 / Real.log γ₁ * Real.log (σbar / σ 0)⌉ := by sorry

end AdaptiveCubic.Cauchy
