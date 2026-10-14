-- Prove2me | Theorems.Thm_FactorRMDP_Blackwell_proposition_6_1_2
-- name    : FactorRMDP.Blackwell.proposition_6_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:06.806483+00:00
-- url     : https://prove2.me/theorems/3d45738e-7466-4139-9de4-db9a3ade73e6
-- title:
--   Proposition 6.1.2 — robust maximum principle: an optimal robust pair has the highest worst-case value at every state (p₀ > 0)
-- statement:
--   Let $\mathcal W$ be an $r$-rectangular uncertainty set of factor matrices, let $\lambda\in(0,1)$, and assume $p_0(s)>0$ for every state $s$. Let $(\pi^*,W^*)$ be an optimal solution of the robust MDP problem (1.2): $\pi^*\in\Pi$ maximizes $z_\lambda(\pi)=\min_{W\in\mathcal W}R(\pi,W,\lambda)$ over $\Pi$, and $W^*\in\mathcal W$ attains $\min_{W\in\mathcal W}R(\pi^*,W,\lambda)$. Then for every policy $\pi\in\Pi$ and every $W^1\in\arg\min_{W\in\mathcal W}R(\pi,W,\lambda)$,
--   $$
--   v^{\pi,W^1}_{\lambda,s}\le v^{\pi^*,W^*}_{\lambda,s}\qquad\text{for all }s\in\mathbb S .
--   $$
--
--   This is the **robust maximum principle**: an optimal robust policy achieves the highest worst-case value starting from any state, the robust counterpart of the classical statement that an optimal policy's value function dominates every other policy's componentwise.
--
--   **Formalization Note** The paper states this for every initial distribution $p_0$. As printed it is false when $p_0$ vanishes on some state: a minimizer of $R(\pi,\cdot)$ is then free to be bad at states that $p_0$ never reaches. We therefore assume $p_0>0$ componentwise. Minimizers are expressed with `IsLeast` on the set $\{R(\pi,W,\lambda):W\in\mathcal W\}$, and $0<\lambda<1$ is explicit.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 13, Proposition 6.1, part 2 (proof in Appendix F, pp. 25–26)

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model

namespace FactorRMDP.Blackwell

/-- Proposition 6.1, part 2 (p. 13), the robust maximum principle. If (π*, W*) solves the robust
MDP problem (π* maximizes z_λ over Π and W* minimizes R(π*, ·) over 𝒲), then for every π ∈ Π and
every W¹ minimizing R(π, ·) over 𝒲, v^{π,W¹}_s ≤ v^{π*,W*}_s at every state s.
The paper states this for any initial distribution p₀; it is false when p₀ vanishes on a state
(counterexample in MODERATION_NOTES.md), so we assume p₀ > 0 componentwise (`hp0`). -/
theorem proposition_6_1_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) (hp0 : ∀ s, 0 < M.p0 s)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∀ πs Ws, M.IsRobustSolution lam πs Ws →
      ∀ π ∈ FactorRMDP.ValueIter.Policies S A, ∀ W₁ ∈ M.Wset, IsLeast (M.evalValues lam π) (M.R lam π W₁) →
        ∀ s, M.value lam π W₁ s ≤ M.value lam πs Ws s := by sorry

end FactorRMDP.Blackwell
