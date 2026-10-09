-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_6
-- name    : DynAssortPers.Regret.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:28.230969+00:00
-- url     : https://prove2.me/theorems/0bb8f003-cc03-4f79-bd96-3f328745e90b
-- title:
--   Lemma 6, p. 37 — if $\|\nabla L(\Theta^\star)\|\le\lambda/2$ then $\|\Delta\|_*\le16\max\{\sqrt r\|\Delta\|_F,\|\bar\Theta^\star_r\|_*\}$
-- statement:
--   Let $\mathcal O$ be a sample of observations, $\lambda>0$ and $\alpha\in\mathbb R$. Let $\widehat\Theta$ be a solution of (5), let $\Theta^\star$ satisfy $\|\Theta^\star\|_\infty\le\alpha/\sqrt{mn}$, and put $\Delta=\widehat\Theta-\Theta^\star$. If the spectral norm of the gradient of the loss at $\Theta^\star$ satisfies $\|\nabla L(\Theta^\star)\|_2\le\lambda/2$, then for any $r\in\mathbb N$
--   $$\|\Delta\|_*\le16\max\Big\{\sqrt r\,\|\Delta\|_F,\ \|\bar\Theta^\star_r\|_*\Big\},$$
--   where $\|\bar\Theta^\star_r\|_*=\sum_{j=r+1}^{\min(m,n)}\sigma_j(\Theta^\star)$ is the nuclear norm of the part of $\Theta^\star$ beyond its top $r$ singular directions.
--
--   This is where the (approximate) low rank of $\Theta^\star$ enters the recovery argument: the nuclear-norm error is controlled by the Frobenius error and the tail of the spectrum.
--
--   **Formalization Note** The same standing hypotheses as Lemma 5 ($\widehat\Theta$ solves (5), $\Theta^\star$ feasible, $\lambda>0$) are stated. The unsubscripted norm $\|\nabla L(\Theta^\star)\|$ of the page is the spectral norm, as in Lemma 4 and the proof (p. 43). The tail is written through Mathlib's singular values (0-based, decreasing): the paper's $\sigma_j$ is index $j-1$, and for $r\ge\min(m,n)$ the tail is $0$. $r$ is any natural number.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Lemma 6, eq. (15), p. 37 (proof pp. 42–43; Θ̄⋆_r on p. 42, its nuclear norm on p. 43)

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator

namespace DynAssortPers.Regret

open MatrixCompletion

/-- Lemma 6 (p. 37, (15)): if `Θ̂` solves (5) for the sample `𝒪` and `λ > 0`, `Θ⋆` is feasible
for (5) and `‖∇L(Θ⋆)‖₂ ≤ λ/2`, then for any `r`, with `Δ = Θ̂ − Θ⋆`,
`‖Δ‖_* ≤ 16 max{√r ‖Δ‖_F, ‖Θ̄⋆_r‖_*}`, where `‖Θ̄⋆_r‖_* = ∑_{j=r+1}^{min(m,n)} σ_j(Θ⋆)`. -/
theorem lemma_6 {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh)
    (hgrad : spectralNorm (lossGrad O Θs) ≤ lam / 2) (r : ℕ) :
    nuclearNorm (Θh - Θs) ≤
      16 * max (Real.sqrt (r : ℝ) * frobeniusNorm (Θh - Θs)) (tailNuclear Θs r) := by sorry

end DynAssortPers.Regret
