-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_Supplement_lemma_8_2
-- name    : ConcurrentStochasticApprox.Approx.Supplement.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:14.04453+00:00
-- url     : https://prove2.me/theorems/9821291c-e0cb-4940-b559-93702b8858aa
-- title:
--   Lemma 8.2 (used in the proof of Theorem 4.1) — Real stationary witnesses
-- statement:
--   Let $G$ be a concurrent stochastic game with $n\ge1$ states and nonempty action sets, $r:S\times A\times B\to[0,1]$, $0\le\lambda<1$, $s\in S$ and $c\in\mathbb R$. Write $G_\sigma$ and $G_\tau$ for the MDPs obtained by fixing the indicated stationary strategy, with the induced reward function. Their Bellman operators take the minimum over Player 2's actions and the maximum over Player 1's actions, respectively. Then both equivalences hold:
--   $$
--   \operatorname{val}_\lambda(s)>c\iff\exists\sigma\in\Sigma_S\ \exists L:S\to\mathbb R,\quad L\preceq\Psi_{G_\sigma}(L)\ \land\ L(s)>c,
--   $$
--   $$
--   \operatorname{val}_\lambda(s)<c\iff\exists\tau\in\Gamma_S\ \exists U:S\to\mathbb R,\quad\Psi_{G_\tau}(U)\preceq U\ \land\ U(s)<c.
--   $$
--   The Bellman inequalities hold at every state. The functions $L,U$ are arbitrary real functions, and the discount is an arbitrary real discount in the indicated interval. These equivalences supply real witnesses for strict value comparisons.
--
--   Differences from the source:
--   - encoding: finite state and action sets with pointwise function order → zero-based Fin indices and the published CSG and Bellman interfaces; reason: index relabeling and pointwise order preserve every game and both witness equivalences
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), Lemma 8.2, printed 35 (PDF 37)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Game

namespace ConcurrentStochasticApprox.Approx.Supplement

/-- Lemma 8.2, both real-witness equivalences for every real discount in [0,1). -/
theorem lemma_8_2 {n mA mB : ℕ} (G : CSG n mA mB) (r : Reward n mA mB)
    (hr : IsReward r) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam < 1) (s : Fin n) (c : ℝ) :
    (discValue G r lam s > c ↔
      ∃ (σ : Stationary₁ n mA) (L : Fin n → ℝ),
        L ≤ bellman₂ (fixP1 G σ) (fixP1Reward r σ) lam L ∧ L s > c) ∧
    (discValue G r lam s < c ↔
      ∃ (τ : Stationary₂ n mB) (U : Fin n → ℝ),
        bellman₁ (fixP2 G τ) (fixP2Reward r τ) lam U ≤ U ∧ U s < c) := by sorry

end ConcurrentStochasticApprox.Approx.Supplement
