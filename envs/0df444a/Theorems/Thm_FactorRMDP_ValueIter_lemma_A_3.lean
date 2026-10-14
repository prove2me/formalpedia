-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_lemma_A_3
-- name    : FactorRMDP.ValueIter.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:27.272986+00:00
-- url     : https://prove2.me/theorems/782132ed-848a-4ac2-8f98-d819a9371a4e
-- title:
--   Lemma A.3 — min_W p₀ᵀT_π(I − λWᵀT_π)⁻¹Wᵀr_π = min_W max{p₀ᵀT_πβ | β ≤ Wᵀ(r_π + λT_πβ)}
-- statement:
--   Consider a robust MDP with factor matrix uncertainty set $\mathcal W$ (not necessarily r-rectangular), a discount factor $\lambda\in(0,1)$ and a stationary policy $\pi\in\Pi$. For every $W\in\mathcal W$, the linear program
--
--   $$\max\ p_0^\top T_\pi\beta \quad\text{subject to}\quad \beta \le W^\top(r_\pi + \lambda T_\pi\beta),\ \ \beta\in\mathbb R^r,$$
--
--   attains its maximum. The minimum over $W\in\mathcal W$ of those optimal values equals the minimum of $p_0^\top T_\pi(I-\lambda W^\top T_\pi)^{-1}W^\top r_\pi$, as in (A.2)–(A.4):
--
--   $$\min_{W\in\mathcal W} p_0^\top T_\pi(I-\lambda W^\top T_\pi)^{-1}W^\top r_\pi = \min_{W\in\mathcal W}\ \max\{ p_0^\top T_\pi\beta \mid \beta\in\mathbb R^r,\ \beta\le W^\top(r_\pi+\lambda T_\pi\beta)\}.$$
--
--   The inequality $\le$ between vectors is componentwise.
--
--   **Formalization Note** The statement is the displayed minimum identity (A.2)–(A.4). The inner maxima and outer minima are attained; `IsGreatest` and `IsLeast` make this explicit.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 21, Lemma A.3, (A.2)–(A.4), proof (A.7)–(A.10)

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Lemma A.3 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 21), (A.2)–(A.4).
For any factor matrix uncertainty set (no r-rectangularity) and `π ∈ Π`, the minimum over
`W ∈ 𝒲` of `p₀ᵀ T_π (I − λ WᵀT_π)⁻¹ Wᵀ r_π` equals the minimum over `W ∈ 𝒲` of the maximum
`p₀ᵀ T_π β` subject to `β ≤ Wᵀ(r_π + λ T_π β)`. The inner maxima and both outer minima are
attained. -/
theorem lemma_A_3 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : S → A → ℝ) (hπ : π ∈ Policies S A) :
    let g : (Fin r → S → ℝ) → ℝ := fun W =>
      M.p0 ⬝ᵥ (M.T π *ᵥ ((1 - lam • ((wmat W)ᵀ * M.T π))⁻¹ *ᵥ ((wmat W)ᵀ *ᵥ M.rpi π)))
    let feasible : (Fin r → S → ℝ) → Set ℝ := fun W =>
      {x | ∃ β : Fin r → ℝ,
        β ≤ (wmat W)ᵀ *ᵥ (M.rpi π + lam • (M.T π *ᵥ β)) ∧
        x = M.p0 ⬝ᵥ (M.T π *ᵥ β)}
    let h : (Fin r → S → ℝ) → ℝ := fun W => sSup (feasible W)
    (∀ W ∈ M.Wset, ∃ x, IsGreatest (feasible W) x) ∧
      ∃ Wg ∈ M.Wset, ∃ Wh ∈ M.Wset,
        IsLeast (g '' M.Wset) (g Wg) ∧
        IsLeast (h '' M.Wset) (h Wh) ∧ g Wg = h Wh := by sorry

end FactorRMDP.ValueIter
