-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_marginal_subset_spreadSet
-- name    : DRConvexOpt.Spread.marginal_subset_spreadSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:38.305334+00:00
-- url     : https://prove2.me/theorems/920b064d-5d0f-460c-9ccc-e20b8b8fffb8
-- title:
--   Proof of Proposition 2, pp. 40–41 — Π_z̃𝒫 is contained in the absolute-mean-spread set
-- statement:
--   Let $f\in\mathbb R^P$, $\theta\in\mathbb R$, $\sigma\ge0$ and $\rho\in(0,1)$, and let $\mathcal P$ be the lifted ambiguity set of Proposition 2: distributions $\mathbb P$ of $(\tilde z,\tilde u,\tilde v,\tilde w)$ on $\mathbb R^P\times\mathbb R^3$ with $\mathbb E_{\mathbb P}[\tilde w]=\sigma$, $\mathbb P[f^\top\tilde z\ge\theta]=\rho$ and, almost surely, $f^\top\tilde z=\theta+\tilde u-\tilde v$, $\tilde w\ge\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v$, $\tilde u,\tilde v\ge0$. Then
--
--   $$
--   \Pi_{\tilde z}\mathcal P\subseteq\big\{\mathbb Q\in\mathcal P_0(\mathbb R^P):\ \mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta]\le\sigma,\ \mathbb Q[f^\top\tilde z\ge\theta]=\rho\big\}.
--   $$
--
--   This is the first of the two inclusions that make up Proposition 2.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. An outcome is $\omega=(z,(u,v,w))\in\mathbb R^P\times(\mathbb R\times\mathbb R\times\mathbb R)$, with $\tilde u,\tilde v,\tilde w$ the projections `uOf`, `vOf`, `wOf`; the marginal $\Pi_{\tilde z}\mathbb P$ is the push-forward of $\mathbb P$ under the first projection. Integrability of $\tilde u$, $\tilde v$ and $f^\top\tilde z$ under $\mathbb P$ is not assumed: it follows from $0\le\tilde u\le\rho\tilde w$, $0\le\tilde v\le(1-\rho)\tilde w$ almost surely and the integrability of $\tilde w$. The right-hand side is the set of probability distributions $\mathbb Q$ on $\mathbb R^P$ with $f^\top\tilde z$ integrable, $\mathbb Q[f^\top\tilde z\ge\theta]=\rho$ and $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta]\le\sigma$.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 40–41, proof of Proposition 2, first inclusion

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proof of Proposition 2, pp. 40–41: `Π_z̃𝒫` is contained in the set of distributions `Q` with
`Q[fᵀz̃ ≥ θ] = ρ` and absolute mean spread at most `σ`. -/
theorem marginal_subset_spreadSet {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hσ : 0 ≤ σ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (fun μ => μ.map Prod.fst) '' liftedSpreadSet f θ σ ρ ⊆ spreadSet f θ σ ρ := by sorry

end DRConvexOpt.Spread
