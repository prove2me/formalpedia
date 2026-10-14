-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_E_1
-- name    : FactorRMDP.ValueIter.lemma_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:43.341908+00:00
-- url     : https://prove2.me/theorems/a3d2968d-82ab-46ef-973e-847b29a2837d
-- title:
--   Lemma E.1 — F is componentwise non-decreasing and a λ-contraction in ‖·‖∞
-- statement:
--   Consider a robust MDP with factor matrix uncertainty and a discount factor $\lambda\in(0,1)$. Let $F:\mathbb R^S\to\mathbb R^S$ be
--
--   $$F(v)_s = \max_{a\in\mathbb A}\Big\{ r_{sa} + \lambda\sum_{i=1}^r u^i_{sa}\min_{w_i\in\mathcal W^i} w_i^\top v\Big\}, \qquad s\in\mathbb S.$$
--
--   Then $F$ is componentwise non-decreasing and a contraction:
--
--   $$\|F(v_1) - F(v_2)\|_\infty \le \lambda\,\|v_1-v_2\|_\infty \qquad\text{for all } v_1,v_2\in\mathbb R^S.$$
--
--   Consequently $F$ has a unique fixed point and Algorithm VI-PI converges to it.
--
--   **Formalization Note** Appendix E writes $F$ on $\mathbb R^S_+$ with a maximum over $\pi_s\in\Delta$; §5 (p. 10) defines it on $\mathbb R^S$ and states the deterministic form equivalent. We use $\mathbb R^S$ and the maximum over actions. No r-rectangularity is assumed.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 25, Appendix E, Lemma E.1; F defined p. 10

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma E.1 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 25). The operator
`F(v)_s = max_{a ∈ 𝔸} { r_sa + λ ∑ᵢ u^i_sa min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ v }` is componentwise non-decreasing and a
`λ`-contraction in the sup norm: `‖F(v₁) − F(v₂)‖_∞ ≤ λ ‖v₁ − v₂‖_∞`. Stated on `ℝ^S`, the domain of
`F` in §5 (p. 10); Appendix E writes `ℝ^S_+`. No r-rectangularity is assumed. -/
theorem lemma_E_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Monotone (M.F lam) ∧ ∀ v₁ v₂ : S → ℝ, ‖M.F lam v₁ - M.F lam v₂‖ ≤ lam * ‖v₁ - v₂‖ := by sorry

end FactorRMDP.ValueIter
