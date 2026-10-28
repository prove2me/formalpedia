-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_9
-- name    : DiscreteSearchGame.Optimal.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:55.384652+00:00
-- url     : https://prove2.me/theorems/4b69b2f1-a4a1-4c52-8542-db627b44d5c7
-- title:
--   Lemma 9, p. 15 — for interior p the convex hull of 𝒮_p equals the convex hull of 𝒮̂_p
-- statement:
--   For any hiding strategy $p=(p_1,\dots,p_n)$ with $p_i>0$ for $i=1,\dots,n$,
--   $$\operatorname{Conv}(\mathcal S_p)=\operatorname{Conv}(\widehat{\mathcal S}_p),$$
--   where $\mathcal S_p=\{V(\xi):\xi\in\mathcal C_p\}$ is the set of payoff vectors of all Gittins search sequences against $p$ and $\widehat{\mathcal S}_p=\{V(\xi_{\sigma,p}):\sigma\in S_n\}$ those of the Gittins search sequences that break every tie by one preference ordering $\sigma$.
--
--   So any mixture of Gittins search sequences against $p$ has the payoff vector of some mixture of the at most $n!$ sequences $\xi_{\sigma,p}$.
--
--   **Formalization Note.** `[NeZero n]` is needed to construct $\xi_{\sigma,p}$ and is implied by $p$ lying in the simplex. Payoff vectors are taken in $\mathbb R^n$ via `toReal`; they are finite for interior $p$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 15, Lemma 9 (proof pp. 16–20)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 9, p. 15: for interior `p`, `Conv(𝒮_p) = Conv(𝒮̂_p)`. -/
theorem lemma_9 {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ i, 0 < p i) :
    convexHull ℝ (payoffSet t q p) = convexHull ℝ (simplePayoffSet t q p) := by sorry

end DiscreteSearchGame.Optimal
