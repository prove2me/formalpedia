-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_4_1
-- name    : FactorRMDP.ValueIter.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:29.417983+00:00
-- url     : https://prove2.me/theorems/f6ce82ad-37e0-4c29-a950-a4ca754e48fd
-- title:
--   Lemma 4.1 — under r-rectangularity a stationary deterministic policy solves the policy improvement problem
-- statement:
--   Consider a robust MDP whose factor matrix uncertainty set is r-rectangular and a discount factor $\lambda\in(0,1)$. Then there exists a stationary and deterministic policy $\pi^*\in\Pi$ that solves the policy improvement problem
--
--   $$z^* = \max_{\pi\in\Pi} z(\pi) = z(\pi^*), \qquad z(\pi) = \min_{W\in\mathcal W} R(\pi,W).$$
--
--   In particular the maximum over $\Pi$ is attained, and randomization does not help the decision maker.
--
--   **Formalization Note** The policy improvement problem is taken over stationary policies $\Pi$, as the paper does after Proposition 2.5 (p. 5). The oracle part of Assumption 2.4 plays no role and is not formalized.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 7, Lemma 4.1, (4.1)–(4.3)

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma 4.1 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 7). If the uncertainty set is
r-rectangular, some stationary deterministic policy solves the policy improvement problem
`z* = max_{π ∈ Π} z(π)` of (4.1). -/
theorem lemma_4_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    ∃ π : S → A → ℝ, IsDeterministic π ∧ π ∈ Policies S A ∧
      IsGreatest (M.z lam '' Policies S A) (M.z lam π) := by sorry

end FactorRMDP.ValueIter
