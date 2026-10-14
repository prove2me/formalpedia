-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_4_3
-- name    : FactorRMDP.ValueIter.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:30.962048+00:00
-- url     : https://prove2.me/theorems/723d659a-d003-4a8e-af60-4b3de92124b3
-- title:
--   Lemma 4.3 — Wᵀv = β: the adversary's value is Wᵀ times the decision maker's value
-- statement:
--   Consider a robust MDP with factor matrix uncertainty and a discount factor $\lambda\in(0,1)$. Let $\pi \in \Pi$ and $W \in \mathcal W$, let $v = v^{\pi,W}$ be the value function of the decision maker and $\beta = \beta^{\pi,W}$ the value function of the adversary. Then
--
--   $$W^\top v = \beta, \qquad\text{i.e.}\qquad w_i^\top v = \beta_i \ \text{ for every } i\in[r].$$
--
--   The lemma links the two value functions; it is how the decision maker's optimality equation is rewritten in terms of factor-wise minima.
--
--   **Formalization Note** Both value functions are discounted sums (`value`, `advValue`). No r-rectangularity is assumed.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 8, Lemma 4.3

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma 4.3 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 8). Let `π ∈ Π` and `W ∈ 𝒲`. Let `v`
be the value function of the decision maker (the discounted sum `value`) and `β` the value function
of the adversary (the discounted sum `advValue`). Then `Wᵀv = β`. -/
theorem lemma_4_3 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : S → A → ℝ) (hπ : π ∈ Policies S A) (W : Fin r → S → ℝ) (hW : W ∈ M.Wset) :
    (wmat W)ᵀ *ᵥ M.value lam π W = M.advValue lam π W := by sorry

end FactorRMDP.ValueIter
