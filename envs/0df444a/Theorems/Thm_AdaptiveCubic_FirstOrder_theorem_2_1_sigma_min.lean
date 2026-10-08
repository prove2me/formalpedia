-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_theorem_2_1_sigma_min
-- name    : AdaptiveCubic.FirstOrder.theorem_2_1_sigma_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:30.833445+00:00
-- url     : https://prove2.me/theorems/11443c0a-233f-41bd-a476-0a6507c85051
-- title:
--   Theorem 2.1, (2.14) — the bound on |U_j| when σ_k ≥ σ_min
-- statement:
--   Consider a run of ARC (Algorithm 2.1) with $\gamma_1>1$, and suppose (2.11): $\sigma_k\ge\sigma_{\min}$ for all $k$, for some $\sigma_{\min}>0$. Fix $j\ge0$ and let $\mathcal S_j$ and $\mathcal U_j$ be the successful and unsuccessful iterations $k\le j$ (2.9). If $\bar\sigma>0$ satisfies $\sigma_k\le\bar\sigma$ for all $k\le j+1$, then
--
--   $$|\mathcal U_j|\le\left\lceil(|\mathcal S_j|+1)\,\frac{1}{\log\gamma_1}\,\log\frac{\bar\sigma}{\sigma_{\min}}\right\rceil.$$
--
--   This is the form of Theorem 2.1 used for ARC(S), where $\sigma_k$ is bounded below by (2.11) and above by Lemma 5.1; in the proof of Corollary 5.3 it is applied with $\bar\sigma=L_0$.
--
--   **Formalization Note** As for (2.13), the upper bound (2.12) is assumed for $k\le j+1$ instead of the printed $k\le j$: the printed statement fails for $j=0$, iteration $0$ unsuccessful, $\bar\sigma=\sigma_0=\sigma_{\min}$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 5, Theorem 2.1, (2.14)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Theorem 2.1, (2.14), p. 5 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
For any fixed `j ≥ 0`, if `σ_k ≥ σ_min > 0` for all `k` (2.11) and `σ̄ > 0` bounds `σ_k`, then
`|U_j| ≤ ⌈(|S_j| + 1)(1/log γ₁) log(σ̄/σ_min)⌉`, with `S_j`, `U_j` the successful and
unsuccessful iterations `k ≤ j` (2.9).

Correction: (2.12) is posed for `k ≤ j + 1` instead of `k ≤ j` (the proof bounds `σ_{j+1}`; the
printed statement fails for `j = 0`, iteration `0` unsuccessful, `σ̄ = σ₀ = σ_min`). -/
theorem theorem_2_1_sigma_min {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (j : ℕ) (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈((((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) + 1) *
        (1 / Real.log γ₁) * Real.log (σbar / σmin)⌉ := by sorry

end AdaptiveCubic.FirstOrder
