-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_phi_contraction
-- name    : FactorRMDP.ValueIter.phi_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:28.698096+00:00
-- url     : https://prove2.me/theorems/2283c3e1-4ea1-4cd9-930b-b82add38545b
-- title:
--   Appendix A, p. 22 — φ(π, ·) is componentwise non-decreasing and a λ-contraction in ‖·‖∞
-- statement:
--   Consider a robust MDP with factor matrix uncertainty, a discount factor $\lambda\in(0,1)$ and a stationary policy $\pi\in\Pi$. Define $\varphi(\pi,\cdot):\mathbb R^r\to\mathbb R^r$ by
--
--   $$\varphi(\pi,\beta)_i = \min_{w_i\in\mathcal W^i} w_i^\top\big(r_\pi + \lambda T_\pi\beta\big), \qquad i\in[r].$$
--
--   Then $\varphi(\pi,\cdot)$ is componentwise non-decreasing ($\beta_1\le\beta_2$ implies $\varphi(\pi,\beta_1)\le\varphi(\pi,\beta_2)$) and a contraction:
--
--   $$\|\varphi(\pi,\beta_1) - \varphi(\pi,\beta_2)\|_\infty \le \lambda\,\|\beta_1-\beta_2\|_\infty \qquad\text{for all } \beta_1,\beta_2\in\mathbb R^r.$$
--
--   Its fixed point is the adversary's optimal value function, and its iterates from $0$ form Algorithm VI-PE.
--
--   **Formalization Note** The paper writes $\varphi$ on $\mathbb R^r_+$; its argument does not use the sign of $\beta$, and $\beta\in\mathbb R^r$ is where $\varphi$ is used in (3.3)–(3.5), so the statement is on $\mathbb R^r$. The norm on `Fin r → ℝ` is the sup norm. No r-rectangularity is assumed.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), Appendix A, proof of Theorem 3.2, p. 22

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Appendix A, proof of Theorem 3.2 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 22). For
`π ∈ Π`, the map `φ(π, ·) : ℝ^r → ℝ^r`, `φ(π, β)ᵢ = min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ(r_π + λ T_π β)`, is
componentwise non-decreasing and a `λ`-contraction in the sup norm:
`‖φ(π, β₁) − φ(π, β₂)‖_∞ ≤ λ ‖β₁ − β₂‖_∞`. Stated on all of `ℝ^r` (the page writes `ℝ^r_+`; its
argument does not use the sign of `β`). No r-rectangularity is assumed. -/
theorem phi_contraction {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : S → A → ℝ) (hπ : π ∈ Policies S A) :
    Monotone (M.phi lam π) ∧
      ∀ β₁ β₂ : Fin r → ℝ, ‖M.phi lam π β₁ - M.phi lam π β₂‖ ≤ lam * ‖β₁ - β₂‖ := by sorry

end FactorRMDP.ValueIter
