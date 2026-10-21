-- Prove2me | Theorems.Thm_AccelMM_BTMap_lemma_3_4
-- name    : AccelMM.BTMap.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:04.464721+00:00
-- url     : https://prove2.me/theorems/195ac224-4955-4b00-b3c0-c19a44690520
-- title:
--   Lemma 3.4, p. 9 — −ρ is e^{−ω}β-strongly convex and ((1/4)λ_n(L_M) + e^{ω}β)-smooth on W_ω
-- statement:
--   Let $\alpha\ge1$, $\beta>0$, $\omega\ge0$, let $d_{i,j}$ be the comparison counts and $W_\omega=\{w\in\mathbb R^n:\|w\|_\infty\le\omega\}$. The negative log-a posteriori function $-\rho$ of the Bradley–Terry model with $\mathrm{Gamma}(\alpha,\beta)$ prior is $\gamma$-strongly convex and $\mu$-smooth on $W_\omega$ with
--   $$\gamma=e^{-\omega}\beta\qquad\text{and}\qquad\mu=\tfrac14\lambda_n(L_M)+e^{\omega}\beta,$$
--   where $\lambda_n(L_M)$ is the largest eigenvalue of the Laplacian $L_M$.
--
--   Strong convexity is meant in the paper's subgradient form (p. 7), smoothness as a Lipschitz bound on $\nabla(-\rho)$ over $W_\omega$. The strong-convexity constant is proportional to $\beta$, which is why plain MAP iterations can be slow for small $\beta$.
--
--   **Formalization Note** $\alpha\ge1$ and $\beta>0$ are the standing assumptions on the Gamma prior (§2, p. 5).
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 9, Lemma 3.4

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem lemma_3_4 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 ≤ α) (hβ : 0 < β) (hω : 0 ≤ ω) :
    StronglyConvexOn (fun w => -rho α β d w) (box ω) (Real.exp (-ω) * β) ∧
      SmoothOn (fun w => -rho α β d w) (box ω) (1 / 4 * lamMax d + Real.exp ω * β) := by sorry

end AccelMM.BTMap
