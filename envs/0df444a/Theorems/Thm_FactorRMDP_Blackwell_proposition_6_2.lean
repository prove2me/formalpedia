-- Prove2me | Theorems.Thm_FactorRMDP_Blackwell_proposition_6_2
-- name    : FactorRMDP.Blackwell.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:28:17.821259+00:00
-- url     : https://prove2.me/theorems/3b712982-dca8-4e96-8f58-38eb3a4f2f37
-- title:
--   Proposition 6.2 — robust Blackwell optimality: one deterministic policy and factor matrix are robust-optimal for every discount near 1
-- statement:
--   Let $\mathcal W$ be an $r$-rectangular uncertainty set of factor matrices, and assume that each factor set $\mathcal W^1,\dots,\mathcal W^r$ has finitely many extreme points (for instance, each is a polytope). Then there exist a stationary deterministic policy $\pi^*$, a factor matrix $W^*\in\mathcal W$ and a discount factor $\lambda_0\in(0,1)$ such that
--   $$
--   \forall\,\lambda\in(\lambda_0,1):\qquad (\pi^*,W^*)\ \text{is an optimal solution of the robust MDP problem (1.2) with discount }\lambda,
--   $$
--   that is, $\pi^*$ maximizes $z_\lambda(\pi)=\min_{W\in\mathcal W}R(\pi,W,\lambda)$ over all stationary policies and $W^*$ attains $\min_{W\in\mathcal W}R(\pi^*,W,\lambda)$.
--
--   This is the robust counterpart of Blackwell optimality: the same pair is optimal for all discount factors sufficiently close to $1$, with the pair chosen before $\lambda_0$ and independent of $\lambda$.
--
--   **Formalization Note** Optimality is over stationary (possibly randomized) policies, as in (4.1) and in the proof. The initial distribution $p_0$ is arbitrary in $\Delta(\mathbb S)$, as printed; no positivity is assumed. The finiteness hypothesis is on the extreme points of each factor set $\mathcal W^i$ (the projection of $\mathcal W$), as in the paper.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 14, Proposition 6.2 (proof in Appendix G.1, pp. 26–27)

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model

namespace FactorRMDP.Blackwell

/-- Proposition 6.2 (p. 14), robust Blackwell optimality. If 𝒲 is r-rectangular and every
factor set 𝒲ⁱ has finitely many extreme points, there are a stationary deterministic policy π*,
a factor matrix W* ∈ 𝒲 and λ₀ ∈ (0, 1) such that for every λ ∈ (λ₀, 1) the same pair (π*, W*)
is an optimal solution of the robust MDP problem (1.2) with discount λ. -/
theorem proposition_6_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect)
    (hext : ∀ i, (Set.extremePoints ℝ (M.factorSet i)).Finite) :
    ∃ πs : S → A → ℝ, ∃ Ws : Fin r → S → ℝ, ∃ lam0 : ℝ,
      FactorRMDP.ValueIter.IsDeterministic πs ∧ Ws ∈ M.Wset ∧ 0 < lam0 ∧ lam0 < 1 ∧
      ∀ lam : ℝ, lam0 < lam → lam < 1 → M.IsRobustSolution lam πs Ws := by sorry

end FactorRMDP.Blackwell
