-- Prove2me | Theorems.Thm_FactorRMDP_Blackwell_value_rational
-- name    : FactorRMDP.Blackwell.value_rational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:08.169385+00:00
-- url     : https://prove2.me/theorems/93814eee-24ee-4f12-b259-006bd076e371
-- title:
--   Appendix G.1, p. 27 — v^{π,W}_t = (I − tL(π,W))⁻¹ r_π is a rational function of t, continuous on (0, 1)
-- statement:
--   Let $\pi\in\Pi$ be a stationary policy and $W\in\mathcal W$ a factor matrix, with $L(\pi,W)_{ss'}=\sum_{a\in\mathbb A}\pi_{sa}P_{sas'}$. Then:
--
--   1. for every discount $t\in(0,1)$ the matrix $I-tL(\pi,W)$ is invertible and
--   $$
--   v^{\pi,W}_t=(I-tL(\pi,W))^{-1}r_\pi ;
--   $$
--   2. for every state $s$ there are real polynomials $p$ and $q$ such that $q$ has no zero in $(0,1)$ and $v^{\pi,W}_{t,s}=p(t)/q(t)$ for all $t\in(0,1)$.
--
--   So, for a fixed policy and factor matrix, each coordinate of the value function is a rational function of the discount factor, continuous on $(0,1)$; this is what forces two such value functions either to coincide or to cross only finitely often.
--
--   **Formalization Note** The value function is the discounted series $\sum_t t^k L^k r_\pi$, so item 1 is a genuine identity (a Neumann series), and invertibility is stated explicitly because Lean's matrix inverse returns $0$ on singular matrices. No rectangularity is assumed.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 27, Appendix G.1, proof of Proposition 6.2 (Cramer's rule)

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model
open Matrix

namespace FactorRMDP.Blackwell

/-- Appendix G.1, proof of Proposition 6.2 (p. 27): for a stationary policy π and a factor
matrix W ∈ 𝒲, for every t ∈ (0, 1) the matrix I − tL(π, W) is invertible and
v^{π,W}_t = (I − tL(π, W))⁻¹ r_π; consequently each coordinate t ↦ v^{π,W}_{t,s} is, on (0, 1),
a ratio of two real polynomials whose denominator has no zero in (0, 1). -/
theorem value_rational {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    {r : ℕ} (M : Model S A r) (π : S → A → ℝ) (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    (W : Fin r → S → ℝ) (hW : W ∈ M.Wset) :
    (∀ t : ℝ, 0 < t → t < 1 →
      IsUnit (1 - t • M.L π W) ∧ M.value t π W = (1 - t • M.L π W)⁻¹ *ᵥ M.rpi π) ∧
    ∀ s, ∃ p q : Polynomial ℝ, (∀ t : ℝ, 0 < t → t < 1 → q.eval t ≠ 0) ∧
      ∀ t : ℝ, 0 < t → t < 1 → M.value t π W s = p.eval t / q.eval t := by sorry

end FactorRMDP.Blackwell
