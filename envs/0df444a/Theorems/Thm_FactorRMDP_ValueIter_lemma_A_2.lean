-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_A_2
-- name    : FactorRMDP.ValueIter.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:31.881423+00:00
-- url     : https://prove2.me/theorems/94b19912-c155-4c4c-b646-081a1218fa08
-- title:
--   Lemma A.2 — z(π) = p₀ᵀr_π + λ min_{W∈𝒲} p₀ᵀT_π(I − λWᵀT_π)⁻¹Wᵀr_π
-- statement:
--   Consider a robust MDP with factor matrix uncertainty set $\mathcal W$ (not necessarily r-rectangular), a discount factor $\lambda\in(0,1)$ and a stationary policy $\pi\in\Pi$. For $W\in\mathcal W$ put
--
--   $$g(W) = p_0^\top T_\pi\big(I - \lambda W^\top T_\pi\big)^{-1} W^\top r_\pi .$$
--
--   Then for every $W \in \mathcal W$ the $r\times r$ matrix $I - \lambda W^\top T_\pi$ is invertible and $R(\pi, W) = p_0^\top r_\pi + \lambda\, g(W)$; the function $g$ attains its minimum on $\mathcal W$, and
--
--   $$z(\pi) = p_0^\top r_\pi + \lambda \min_{W\in\mathcal W} p_0^\top T_\pi\big(I - \lambda W^\top T_\pi\big)^{-1} W^\top r_\pi ,$$
--
--   with the minimum of $R(\pi,\cdot)$ over $\mathcal W$ attained.
--
--   This rewrites the policy evaluation problem through an $r\times r$ resolvent instead of an $S\times S$ one, the first step towards the adversarial MDP.
--
--   **Formalization Note** Lean's matrix inverse is $0$ on a singular matrix, so invertibility of $I-\lambda W^\top T_\pi$ is stated as a conclusion. The minimum is stated as a least element (`IsLeast`) of the set of values, so attainment is part of the claim.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 20, Lemma A.2, (A.1)

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma A.2 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 20), (A.1). For any factor matrix
uncertainty set (no r-rectangularity) and `π ∈ Π`, write
`g(W) = p₀ᵀ T_π (I − λ WᵀT_π)⁻¹ Wᵀ r_π`. Then for every `W ∈ 𝒲` the matrix `I − λ WᵀT_π` is
invertible and `R(π, W) = p₀ᵀ r_π + λ g(W)`; moreover `g` attains its minimum over `𝒲` at some `W`,
and `p₀ᵀ r_π + λ g(W)` is then the least element of `{R(π, W′) | W′ ∈ 𝒲}`, i.e.
`z(π) = p₀ᵀ r_π + λ min_{W ∈ 𝒲} g(W)`. The invertibility conjunct guards Lean's junk inverse
(`Matrix.inv` is `0` on a singular matrix). -/
theorem lemma_A_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : S → A → ℝ) (hπ : π ∈ Policies S A) :
    let g : (Fin r → S → ℝ) → ℝ := fun W =>
      M.p0 ⬝ᵥ (M.T π *ᵥ ((1 - lam • ((wmat W)ᵀ * M.T π))⁻¹ *ᵥ ((wmat W)ᵀ *ᵥ M.rpi π)))
    (∀ W ∈ M.Wset, IsUnit (1 - lam • ((wmat W)ᵀ * M.T π))) ∧
    (∀ W ∈ M.Wset, M.R lam π W = M.p0 ⬝ᵥ M.rpi π + lam * g W) ∧
    ∃ W ∈ M.Wset, IsLeast (g '' M.Wset) (g W) ∧
      IsLeast (M.evalValues lam π) (M.p0 ⬝ᵥ M.rpi π + lam * g W) := by sorry

end FactorRMDP.ValueIter
