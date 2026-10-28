-- Prove2me | Theorems.Thm_ContextualAuctions_RevEquiv_theorem_2
-- name    : ContextualAuctions.RevEquiv.theorem_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:32.909661+00:00
-- url     : https://prove2.me/theorems/63b11910-30dc-4e0a-8802-ef6b5abcf66b
-- title:
--   Theorem 2, p. 12 (Revenue and Pacing Equivalence) — Ψ^µ is a symmetric equilibrium of every standard auction family, with first-price expected payments
-- statement:
--   Let $\{\mathcal A_\alpha=(r(\alpha),M_\alpha)\}_{\alpha\in A}$ be a family of anonymous standard auctions with an equilibrium oracle $\psi$ satisfying properties 1–4 of §4. Let $\mu\in\mathcal X_0$ be a pacing function with $\mu\in C^*_0(\mu)$, i.e. an equilibrium pacing function for first price auctions, and suppose the strategy $\Psi^\mu(w,B,\alpha)=\psi^\mu_\alpha\big(w^T\alpha/(1+\mu(w,B))\big)$ of display (1) is jointly measurable. Then:
--   1. $\Psi^\mu$ is a symmetric equilibrium for the family $\{\mathcal A_\alpha\}_{\alpha\in A}$ (Definition 4);
--   2. for every buyer type $\theta\in\Theta$, the expected payment under $\Psi^\mu$ equals the expected payment in first price auctions under $\beta^\mu$:
--   $$\mathbb E_{\alpha,\{\theta_i\}_{i=1}^{n-1}}\big[M_\alpha(\Psi^\mu(\theta,\alpha),\{\Psi^\mu(\theta_i,\alpha)\}_i)\big]=\mathbb E_{\alpha,\{\theta_i\}_{i=1}^{n-1}}\big[\beta^\mu(\theta,\alpha)\,\mathbb 1\{\beta^\mu(\theta,\alpha)\ge\max(r(\alpha),\{\beta^\mu(\theta_i,\alpha)\}_i)\}\big].$$
--
--   The same pacing function thus manages budgets in every standard auction, and in expectation every buyer pays the same in all of them: revenue equivalence survives in-expectation budget constraints.
--
--   **Formalization Note** Both expected payments are taken in $[0,\infty]$, so the identity also asserts that the left side is finite. "Buyer $\theta$" is read as every $\theta\in\Theta$. Joint measurability of $\Psi^\mu$ is a hypothesis because the oracle is a black box. The fixed point is the hypothesis $\mu\in\mathcal X_0$, $\mu\in C^*_0(\mu)$, as printed, not the conclusion of Theorem 1.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 12, Theorem 2

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting
import Definitions.Def_ContextualAuctions_RevEquiv_FixedPoint
import Definitions.Def_ContextualAuctions_RevEquiv_Auctions

namespace ContextualAuctions.RevEquiv

open MeasureTheory
open Classical

theorem theorem_2 (M : Model) (hM : M.Standing) (fam : StdFamily M) (hfam : fam.Valid M)
    (μ : Buyer M → ℝ) (hμ : μ ∈ X0 M) (hfix : μ ∈ C0star M μ)
    (hΨ : Measurable (Function.uncurry (Psi M fam μ))) :
    IsSymEq M fam (Psi M fam μ) ∧
    ∀ θ ∈ Theta M,
      ∫⁻ ω, ENNReal.ofReal (payStd M fam (Psi M fam μ) (Psi M fam μ θ) ω) ∂P M =
        ∫⁻ ω, ENNReal.ofReal
          (if wins M (beta M μ) (beta M μ θ) ω then beta M μ θ ω.1 else 0) ∂P M := by sorry

end ContextualAuctions.RevEquiv
