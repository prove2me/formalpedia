-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_15
-- name    : DiscreteSearchGame.Optimal.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:26.21015+00:00
-- url     : https://prove2.me/theorems/85ec6b78-3acf-4c27-9619-0098670a3826
-- title:
--   Lemma 15, p. 41 — for interior p the set 𝒮_p of payoff vectors of Gittins search sequences is closed
-- statement:
--   Let $p$ be a hiding strategy with $p_i>0$ for $i=1,\dots,n$. Then the set of payoff vectors of the Gittins search sequences against $p$,
--   $$\mathcal S_p=\{V(\xi):\xi\in\mathcal C_p\}\subset\mathbb R^n,\qquad V(\xi)=(V_1(\xi),\dots,V_n(\xi)),$$
--   is closed in $\mathbb R^n$.
--
--   This is the first step of the paper's proof that the perturbed game $G(\epsilon)$ has a closed set of payoff vectors.
--
--   **Formalization Note.** `payoffSet t q p` is $\{(\mathrm{toReal}\,V_i(\xi))_i : \xi\in\mathcal C_p\}$; for interior $p$ every $V_i(\xi)$ with $\xi\in\mathcal C_p$ is finite, so the coercion loses nothing.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 41, Lemma 15, (29)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 15, p. 41: for interior `p`, the set `𝒮_p = {V(ξ) : ξ ∈ 𝒞_p}` is closed. -/
theorem lemma_15 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ i, 0 < p i) :
    IsClosed (payoffSet t q p) := by sorry

end DiscreteSearchGame.Optimal
