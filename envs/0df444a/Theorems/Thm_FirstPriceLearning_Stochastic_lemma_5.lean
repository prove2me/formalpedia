-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_lemma_5
-- name    : FirstPriceLearning.Stochastic.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:58.295332+00:00
-- url     : https://prove2.me/theorems/27499448-4840-431f-b9ee-c46b54ce64e5
-- title:
--   Lemma 5, p. 20 — the largest optimal grid bid b⋆(v) is non-decreasing in the value v
-- statement:
--   Let $G$ be any CDF on $[0,1]$, $R(v,b)=(v-b)G(b)$ the expected reward (2), and $\mathcal A=\{1/K,2/K,\dots,1\}$ the bid grid (6) with $K\ge1$. For $v\in[0,1]$ let $b^\star(v)$ be the **largest** maximiser of $b\mapsto R(v,b)$ over $\mathcal A$. Then
--
--   $$
--   0\le v_1\le v_2\le 1\ \Longrightarrow\ b^\star(v_1)\le b^\star(v_2).
--   $$
--
--   With contexts ordered by value, this is the second condition of Definition 3 for the quantized first-price auction: the optimal bid moves up with the value.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 20, Lemma 5

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Lemma 5 (p. 20): on the bid grid `𝒜 = {1/K, …, 1}` of (6), for any HOB law `G` on `[0, 1]`,
the largest maximiser `b⋆(v)` of `b ↦ R(v, b) = (v - b) G(b)` over `𝒜` is non-decreasing in
`v ∈ [0, 1]`. -/
theorem lemma_5 (K : ℕ) (hK : 1 ≤ K) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    MonotoneOn (largestMaximizer μG (gridA K)) (Set.Icc 0 1) := by sorry

end FirstPriceLearning.Stochastic
