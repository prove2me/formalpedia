-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_lemma_1
-- name    : CostlySeeding.EdgeQuery.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:20.36098+00:00
-- url     : https://prove2.me/theorems/62fad8f7-151b-467c-85c1-486ca1bf79f6
-- title:
--   Lemma 1, p. 15 — transfer of approximate maximizers
-- statement:
--   Let $\Gamma_\delta$ and $\Gamma$ be real set functions on an $n$-vertex ground set, with size-$k$ maxima $\mathrm{OPT}_\delta$ and $\mathrm{OPT}$. Suppose $\alpha\ge0$, every size-$k$ set $S$ satisfies $|\Gamma_\delta(S)-\Gamma(S)|\le\epsilon n$, and a size-$k$ set $L$ satisfies $\Gamma_\delta(L)\ge\alpha\mathrm{OPT}_\delta-\beta n$. Then
--
--   $$
--   \Gamma(L)\ge\alpha\mathrm{OPT}-(\beta+(\alpha+1)\epsilon)n.
--   $$
--
--   This transfers an approximation on a uniformly accurate sketch to the original objective.
--
--   **Formalization Note** The nonnegativity of $\alpha$ is added because the printed statement is false when $\alpha<0$.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 15, Lemma 1

import Definitions.Def_CostlySeeding_EdgeQuery_Model

namespace CostlySeeding.EdgeQuery

theorem lemma_1 (n k : ℕ) (Gd Gm : Finset (Fin n) → ℝ)
    (eps alpha beta : ℝ) (ha : 0 ≤ alpha)
    (hclose : ∀ S : Finset (Fin n), S.card = k →
      |Gd S - Gm S| ≤ eps * (n : ℝ))
    (L : Finset (Fin n)) (hL : L.card = k)
    (happrox : alpha * OPTof Gd k - beta * n ≤ Gd L) :
    alpha * OPTof Gm k - (beta + (alpha + 1) * eps) * n ≤ Gm L := by sorry

end CostlySeeding.EdgeQuery
