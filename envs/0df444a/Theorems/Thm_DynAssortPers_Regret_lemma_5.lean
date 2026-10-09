-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_5
-- name    : DynAssortPers.Regret.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:10.312254+00:00
-- url     : https://prove2.me/theorems/b24b0fcf-b3b7-4f02-9fda-592536490309
-- title:
--   Lemma 5, p. 37 — $D_{\Theta^\star}(\Delta)\le\|\nabla L(\Theta^\star)\|_2\|\Delta\|_*+\lambda(\|\Theta^\star\|_*-\|\widehat\Theta\|_*)\le(\|\nabla L(\Theta^\star)\|_2+\lambda)\|\Delta\|_*$
-- statement:
--   Let $\mathcal O$ be a sample of observations, $\lambda>0$ and $\alpha\in\mathbb R$. Let $\widehat\Theta$ be a solution of (5) — it minimizes $L(\Theta)+\lambda\|\Theta\|_*$ over $\|\Theta\|_\infty\le\alpha/\sqrt{mn}$ — and let $\Theta^\star$ satisfy $\|\Theta^\star\|_\infty\le\alpha/\sqrt{mn}$. With $\Delta=\widehat\Theta-\Theta^\star$,
--   $$D_{\Theta^\star}(\Delta)\le\|\nabla L(\Theta^\star)\|_2\,\|\Delta\|_*+\lambda\big(\|\Theta^\star\|_*-\|\widehat\Theta\|_*\big)\le\big(\|\nabla L(\Theta^\star)\|_2+\lambda\big)\|\Delta\|_* ,$$
--   where $\|\cdot\|_2$ is the spectral norm and $\|\cdot\|_*$ the nuclear norm.
--
--   It is the upper bound on the Bregman divergence that the regularized objective provides, used with Lemma 6 in the recovery argument.
--
--   **Formalization Note** The page states the lemma under the standing notation of Sec. 8 ($\Delta=\widehat\Theta-\Theta^\star$ with $\widehat\Theta$ the solution of (5), p. 36); these, the feasibility of $\Theta^\star$ (assumed in Sec. 3.2, p. 13, and used through "the optimality of $\widehat\Theta$") and $\lambda>0$ (from (5)) are hypotheses. The sample is arbitrary.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Lemma 5, eq. (14), p. 37 (proof p. 42)

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator

namespace DynAssortPers.Regret

open MatrixCompletion

/-- Lemma 5 (p. 37, (14)): if `Θ̂` solves (5) for the sample `𝒪` and `λ > 0`, and `Θ⋆` is
feasible for (5), then with `Δ = Θ̂ − Θ⋆`,
`D_{Θ⋆}(Δ) ≤ ‖∇L(Θ⋆)‖₂ ‖Δ‖_* + λ(‖Θ⋆‖_* − ‖Θ̂‖_*) ≤ (‖∇L(Θ⋆)‖₂ + λ) ‖Δ‖_*`. -/
theorem lemma_5 {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh) :
    bregman O Θs (Θh - Θs) ≤
        spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ∧
      spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ≤
        (spectralNorm (lossGrad O Θs) + lam) * nuclearNorm (Θh - Θs) := by sorry

end DynAssortPers.Regret
