-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_2
-- name    : DynAssortPers.Regret.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:02.555992+00:00
-- url     : https://prove2.me/theorems/aa747f42-6cd9-425d-ad02-3f131635311a
-- title:
--   Lemma 2, p. 36 (corrected) — $D_{\Theta^\star}(\Delta)\ge\frac12\,e^{-4\gamma}\frac1{4K}L_{\mathrm{quad}}(\Delta)$
-- statement:
--   Let $\mathcal O=((i_t,j_t,S_t))_{t=1}^N$ be any sample of observations whose offered sets satisfy $|S_t|\le K$, let $\alpha\in\mathbb R$ and $\gamma=2\alpha/\sqrt{mn}$, and let $\Theta^\star,\Delta\in\mathbb R^{m\times n}$ be such that both $\Theta^\star$ and $\Theta^\star+\Delta$ satisfy $\|\cdot\|_\infty\le\alpha/\sqrt{mn}$. Then the Bregman divergence of the loss (4) around $\Theta^\star$ is bounded below by the quadratic function $L_{\mathrm{quad}}(\Delta)=\frac1N\sum_t\frac1{K_t}\sum_{j\in S_t}\Delta_{i_tj}^2$ ($K_t=|S_t|$):
--   $$D_{\Theta^\star}(\Delta)\ge\frac12\cdot\frac1{e^{4\gamma}}\cdot\frac1{4K}\,L_{\mathrm{quad}}(\Delta).$$
--
--   This is the curvature of the multinomial-logit likelihood on the box of (5), the deterministic first step of the recovery argument.
--
--   **Formalization Note** The printed Lemma 2 has no factor $\frac12$, and is false: for $m=n=N=K=1$, $S_1=\{1\}$, $j_1=0$, $\Theta^\star=0$, $\Delta=\alpha=\varepsilon=0.01$, $D_{\Theta^\star}(\Delta)=\log\frac{1+e^{\varepsilon}}2-\frac\varepsilon2\approx1.2500\cdot10^{-5}$, below $e^{-8\varepsilon}\varepsilon^2/4\approx2.3078\cdot10^{-5}$. The Taylor step of the proof (p. 38) omits the $\frac12$ of the second-order remainder. The hypothesis that $\Theta^\star$ and $\Theta^\star+\Delta=\widehat\Theta$ are both feasible for (5) is the setting in which the paper applies the lemma ($\Delta=\widehat\Theta-\Theta^\star$, $\|\Delta\|_\infty\le\gamma$, p. 36). The sample is arbitrary (no sampling law); $\gamma$ is written out in the statement.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Lemma 2, p. 36 (corrected; notation of Sec. 8, p. 36; proof pp. 38–39)

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator

namespace DynAssortPers.Regret

open MatrixCompletion

/-- Lemma 2 (p. 36), in its corrected form (the printed bound lacks the factor `1/2`): for any
sample `𝒪` of observations whose offered sets have size at most `K`, and any `Θ⋆`, `Δ` such that
`Θ⋆` and `Θ⋆ + Δ` both satisfy `‖·‖_∞ ≤ α/√(mn)`, with `γ = 2α/√(mn)`,
`D_{Θ⋆}(Δ) ≥ (1/2) (1/e^{4γ}) (1/(4K)) L_quad(Δ)`. -/
theorem lemma_2 {m n : ℕ} (K : ℕ) (O : List (Obs m n)) (hK : ∀ o ∈ O, o.2.2.card ≤ K)
    (α : ℝ) (Θs Δ : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘΔ : entrySupNorm (Θs + Δ) ≤ α / Real.sqrt ((m : ℝ) * n)) :
    (1 / 2) * (1 / Real.exp (4 * (2 * α / Real.sqrt ((m : ℝ) * n)))) * (1 / (4 * (K : ℝ))) *
        lquad O Δ ≤ bregman O Θs Δ := by sorry

end DynAssortPers.Regret
