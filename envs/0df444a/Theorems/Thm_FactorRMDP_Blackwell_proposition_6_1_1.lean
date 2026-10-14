-- Prove2me | Theorems.Thm_FactorRMDP_Blackwell_proposition_6_1_1
-- name    : FactorRMDP.Blackwell.proposition_6_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:57.808983+00:00
-- url     : https://prove2.me/theorems/4b6dfe4f-278b-4d27-8bcd-11b89cd213cc
-- title:
--   Proposition 6.1.1 — under r-rectangularity, a minimizer of R(π,·) is worst at every state (p₀ > 0)
-- statement:
--   Let $\mathcal W$ be an $r$-rectangular uncertainty set of factor matrices, let $\lambda\in(0,1)$, and assume the initial distribution charges every state, $p_0(s)>0$ for all $s\in\mathbb S$. Let $\pi\in\Pi$ be a stationary policy and let $W^1\in\mathcal W$ minimize the expected reward, $W^1\in\arg\min_{W\in\mathcal W}R(\pi,W,\lambda)$. Then $W^1$ is a worst case simultaneously from every initial state:
--   $$
--   v^{\pi,W^1}_{\lambda,s}\le v^{\pi,W^0}_{\lambda,s}\qquad\text{for all }W^0\in\mathcal W\text{ and all }s\in\mathbb S .
--   $$
--
--   So under $r$-rectangularity the worst case of a policy does not depend on the initial distribution; this is the first half of the robust maximum principle.
--
--   **Formalization Note** The paper states this for every initial distribution $p_0$. As printed it is false when $p_0$ vanishes on some state: a minimizer of $R(\pi,\cdot)$ is then free to be bad at states that $p_0$ never reaches. We therefore assume $p_0>0$ componentwise. Minimizers are expressed with `IsLeast` on the set $\{R(\pi,W,\lambda):W\in\mathcal W\}$, and $0<\lambda<1$ is explicit.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 13, Proposition 6.1, part 1 (proof in Appendix F, p. 25)

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model

namespace FactorRMDP.Blackwell

/-- Proposition 6.1, part 1 (p. 13). Under r-rectangularity, a factor matrix W¹ that minimizes
R(π, ·) over 𝒲 is worst at every state: v^{π,W¹}_s ≤ v^{π,W⁰}_s for all W⁰ ∈ 𝒲 and s ∈ 𝕊.
The paper states this for any initial distribution p₀; it is false when p₀ vanishes on a state
(counterexample in MODERATION_NOTES.md), so we assume p₀ > 0 componentwise (`hp0`). -/
theorem proposition_6_1_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) (hp0 : ∀ s, 0 < M.p0 s)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∀ π ∈ FactorRMDP.ValueIter.Policies S A, ∀ W₁ ∈ M.Wset, IsLeast (M.evalValues lam π) (M.R lam π W₁) →
      ∀ W₀ ∈ M.Wset, ∀ s, M.value lam π W₁ s ≤ M.value lam π W₀ s := by sorry

end FactorRMDP.Blackwell
