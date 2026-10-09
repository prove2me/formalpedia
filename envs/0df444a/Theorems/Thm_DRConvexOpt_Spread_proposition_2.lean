-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_proposition_2
-- name    : DRConvexOpt.Spread.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:38.74969+00:00
-- url     : https://prove2.me/theorems/c9f55aea-870f-4a03-a543-b41c46eed15a
-- title:
--   Proposition 2 (Absolute Mean Spread), pp. 17–18 — Π_z̃𝒫 is exactly the set of Q with Q[fᵀz̃ ≥ θ] = ρ and absolute mean spread ≤ σ
-- statement:
--   Let $f\in\mathbb R^P$, $\theta\in\mathbb R$, $\sigma\ge0$ and $\rho\in(0,1)$, and consider the instance of the ambiguity set (4) with auxiliary random variables $\tilde u,\tilde v,\tilde w\in\mathbb R$:
--
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^P\times\mathbb R^3):\ \mathbb E_{\mathbb P}[\tilde w]=\sigma,\ \mathbb P\big[f^\top\tilde z=\theta+\tilde u-\tilde v,\ \tilde w\ge\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v,\ \tilde u,\tilde v\ge0\big]=1,\ \mathbb P[f^\top\tilde z\ge\theta]=\rho\Big\}.
--   $$
--
--   Then
--
--   $$
--   \Pi_{\tilde z}\mathcal P=\Big\{\mathbb Q\in\mathcal P_0(\mathbb R^P):\ \mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta]\le\sigma,\ \mathbb Q[f^\top\tilde z\ge\theta]=\rho\Big\}.
--   $$
--
--   In particular every distribution $\mathbb Q^0$ whose absolute mean spread at $\theta$ is at most $\sigma$ and with $\mathbb Q^0[f^\top\tilde z\ge\theta]=\rho$ is a marginal of a member of $\mathcal P$. Hence an ambiguity set defined by absolute mean spread information is the projection of an instance of the paper's standardized ambiguity set, and worst-case expectation constraints over it fall within the paper's framework.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. An outcome is $\omega=(z,(u,v,w))\in\mathbb R^P\times(\mathbb R\times\mathbb R\times\mathbb R)$, with $\tilde u,\tilde v,\tilde w$ the projections `uOf`, `vOf`, `wOf`; the marginal $\Pi_{\tilde z}\mathbb P$ is the push-forward of $\mathbb P$ under the first projection. Members of the right-hand set are required to have $f^\top\tilde z$ integrable, and members of $\mathcal P$ to have $\tilde w$ integrable: these are the expectations the page writes. The page's "$\mathbb Q^0\in\Pi_{\tilde z}\mathcal P$" is the immediate consequence of the set identity, which is what is stated.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 17–18, Proposition 2 (Absolute Mean Spread); proof pp. 40–41

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proposition 2 (Absolute Mean Spread), pp. 17–18: for `f ∈ ℝ^P`, `θ ∈ ℝ`, `σ ≥ 0` and
`ρ ∈ (0, 1)`, the `z̃`-marginals of the lifted set `𝒫` are exactly the distributions `Q` with
`Q[fᵀz̃ ≥ θ] = ρ` and absolute mean spread at most `σ`. -/
theorem proposition_2 {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    spreadSet f θ σ ρ = (fun μ => μ.map Prod.fst) '' liftedSpreadSet f θ σ ρ := by sorry

end DRConvexOpt.Spread
