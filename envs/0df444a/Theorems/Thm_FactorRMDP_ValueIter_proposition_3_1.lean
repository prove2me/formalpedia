-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_proposition_3_1
-- name    : FactorRMDP.ValueIter.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:31.180841+00:00
-- url     : https://prove2.me/theorems/919b2366-05f7-45f7-b981-41ce3366ed17
-- title:
--   Proposition 3.1 — the adversary's value satisfies the Bellman recursion βᵢ = wᵢᵀ(r_π + λT_πβ)
-- statement:
--   Consider a robust MDP with factor matrix uncertainty, a discount factor $\lambda \in (0,1)$, a stationary policy $\pi \in \Pi$, and factors $w_1 \in \mathcal W^1, \dots, w_r \in \mathcal W^r$ forming $W = (w_1,\dots,w_r)$. Let $\beta \in \mathbb R^r$ be the adversary's value function in the adversarial MDP (3.1), i.e. $\beta = \sum_{t\ge0}\lambda^t (W^\top T_\pi)^t W^\top r_\pi$. Then $\beta$ satisfies the Bellman recursion
--
--   $$\beta_i = w_i^\top\big(r_\pi + \lambda\, T_\pi \beta\big), \qquad i \in [r].$$
--
--   This is the policy-evaluation counterpart of the classical Bellman equation, written for the MDP played by the adversary over the factors.
--
--   **Formalization Note** $\beta$ is the discounted sum `advValue`, so the recursion is a theorem, not a definition. Factors are indexed by `Fin r`. No r-rectangularity is assumed: each $w_i$ only has to lie in $\mathcal W^i$.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 6, Proposition 3.1, (3.2)

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Proposition 3.1 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 6). Let `π ∈ Π` and let the
adversary choose factors `w₁ ∈ 𝒲¹, …, w_r ∈ 𝒲^r`. The adversary's value function `β` (the discounted
sum `advValue` of the adversarial MDP (3.1)) satisfies the Bellman recursion (3.2):
`βᵢ = wᵢᵀ(r_π + λ T_π β)` for all `i ∈ [r]`. No r-rectangularity is assumed: the factors are only
required to lie in the factor sets `𝒲ⁱ`. -/
theorem proposition_3_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : S → A → ℝ) (hπ : π ∈ Policies S A) (W : Fin r → S → ℝ) (hW : ∀ i, W i ∈ M.factorSet i) :
    ∀ i, M.advValue lam π W i = W i ⬝ᵥ (M.rpi π + lam • (M.T π *ᵥ M.advValue lam π W)) := by sorry

end FactorRMDP.ValueIter
