-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_theorem_2_1
-- name    : AdaptiveCubic.SecondOrder.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:07.711364+00:00
-- url     : https://prove2.me/theorems/be06da85-5880-4384-8893-b462cb4a9ab3
-- title:
--   Theorem 2.1 (2.13) — unsuccessful iterations bounded by successful ones
-- statement:
--   Consider a run of the ARC algorithm and fix $j\ge0$. Let $\mathcal S_j=\{k\le j: \rho_k\ge\eta_1\}$ and $\mathcal U_j=\{k\le j:\rho_k<\eta_1\}$ be the successful and unsuccessful iterations up to $j$ (2.9). Assume (2.10): for some $\gamma_3\in(0,1]$, $\sigma_{k+1}\ge\gamma_3\sigma_k$ on every very successful iteration $k\le j$. Let $\bar\sigma>0$ satisfy $\sigma_k\le\bar\sigma$ for all $k\le j+1$. Then
--
--   $$|\mathcal U_j| \le \left\lceil -\frac{\log\gamma_3}{\log\gamma_1}\,|\mathcal S_j| + \frac{1}{\log\gamma_1}\log\frac{\bar\sigma}{\sigma_0}\right\rceil .$$
--
--   The weight grows by at least $\gamma_1$ on every unsuccessful iteration and cannot shrink too fast on successful ones, so a bound on $\sigma_k$ caps the number of unsuccessful iterations in terms of the successful ones. This converts every bound on successful iterations into a bound on all iterations.
--
--   **Formalization Note** The page assumes $\sigma_k\le\bar\sigma$ only for $k\le j$ (2.12). Its proof bounds $\sigma_{j+1}$ (the product in (2.15) covers iterations $0,\dots,j$), and the printed statement fails for $j=0$ with iteration $0$ unsuccessful and $\bar\sigma=\sigma_0$ ($|\mathcal U_0|=1$ but the right-hand side is $0$). The hypothesis is therefore posed for $k\le j+1$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 5, Theorem 2.1, (2.13)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

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
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (j : ℕ) (γ₃ : ℝ) (hγ₃ : 0 < γ₃) (hγ₃' : γ₃ ≤ 1)
    (h210 : ∀ k ≤ j, η₂ < AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1))
    (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈-(Real.log γ₃ / Real.log γ₁) *
          (((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) +
        1 / Real.log γ₁ * Real.log (σbar / σ 0)⌉ := by sorry

end AdaptiveCubic.SecondOrder
