-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_lemma_1
-- name    : DynRiskEq.Welfare.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:38.640512+00:00
-- url     : https://prove2.me/theorems/a9785c92-f1ce-4a0b-b6e8-2e9601194ee1
-- title:
--   Lemma 1, p. 3 — θ is the sup of a linear function over a polytope iff complementary multipliers γ exist
-- statement:
--   Let $\mathcal M$ be a finite sample space, $\mathcal K$ a nonempty finite index set, $p^k\in\mathbb R^{\mathcal M}$ ($k\in\mathcal K$) vectors, and $\mathcal D=\operatorname{conv}\{p^k:k\in\mathcal K\}$. Let $Z\in\mathbb R^{\mathcal M}$ and $\theta\in\mathbb R$. Then
--   $$\theta=\sup_{\mu\in\mathcal D}\sum_{m\in\mathcal M}\mu(m)Z(m)$$
--   if and only if there is $\gamma\in\mathbb R^{\mathcal K}$ with
--   $$\sum_{k\in\mathcal K}\gamma^k=1,\qquad 0\le\gamma^k\ \perp\ \theta-\sum_{m\in\mathcal M}p^k(m)Z(m)\ \ge0\quad(k\in\mathcal K).$$
--   Furthermore, for every such $\gamma$, the vector $\bar\mu(m)=\sum_{k}\gamma^kp^k(m)$ lies in $\mathcal D$ and attains the supremum.
--
--   This turns the evaluation of a polyhedral coherent risk measure into a linear complementarity system, which is how every agent's and the planner's nested risk measures enter the equilibrium systems of the paper.
--
--   **Formalization Note.** The supremum is the real `sSup` of the image of the convex hull, which is nonempty and bounded. $\mathcal K$ is required to be nonempty (an empty risk set has no meaningful supremum and no $\gamma$ sums to one). The paper speaks of the extreme points of $\mathcal D$; the statement is posed for any finite generating family, which includes the extreme points. The $p^k$ need not be probability vectors. Complementarity $0\le y\perp z\ge0$ is $y\ge0$, $z\ge0$, $yz=0$.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), p. 3, Lemma 1

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Lemma 1 (p. 3). For a risk set `𝒟 = conv{p^k, k ∈ 𝒦}` on a finite sample space `ℳ` and a
disbenefit `Z`, `θ = sup_{μ ∈ 𝒟} Σ_m μ(m) Z(m)` iff some `γ` has `Σ_k γ^k = 1` and
`0 ≤ γ^k ⊥ θ − Σ_m p^k(m) Z(m) ≥ 0` for all `k`; and then `μ̄ = Σ_k γ^k p^k` lies in `𝒟` and
attains the supremum. -/
theorem lemma_1 {𝓜 𝓚 : Type} [Fintype 𝓜] [Fintype 𝓚] [Nonempty 𝓚]
    (p : 𝓚 → 𝓜 → ℝ) (Zv : 𝓜 → ℝ) (θ : ℝ) :
    (θ = sSup ((fun μ : 𝓜 → ℝ => ∑ m, μ m * Zv m) '' convexHull ℝ (Set.range p)) ↔
      ∃ γ : 𝓚 → ℝ, ∑ k, γ k = 1 ∧ ∀ k, Compl (γ k) (θ - ∑ m, p k m * Zv m)) ∧
    ∀ γ : 𝓚 → ℝ, (∑ k, γ k = 1 ∧ ∀ k, Compl (γ k) (θ - ∑ m, p k m * Zv m)) →
      (fun m => ∑ k, γ k * p k m) ∈ convexHull ℝ (Set.range p) ∧
      ∑ m, (∑ k, γ k * p k m) * Zv m =
        sSup ((fun μ : 𝓜 → ℝ => ∑ m, μ m * Zv m) '' convexHull ℝ (Set.range p)) := by sorry

end DynRiskEq.Welfare
