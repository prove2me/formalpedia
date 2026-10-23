-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_16
-- name    : DiscreteSearchGame.Optimal.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:19.380991+00:00
-- url     : https://prove2.me/theorems/87992804-1b66-42b5-b10b-36acc6689b2c
-- title:
--   Lemma 16, p. 42 — at a non-tie point p ∈ 𝒫(ε), f(r, ·) is continuous at p for every tie-breaking rule r
-- statement:
--   Let $\epsilon\in(0,1/n)$ and let $p\in\mathcal P(\epsilon)$, i.e. $p$ is a hiding strategy with $p_i\ge\epsilon$ for all $i$. Suppose $p$ is a non-tie point: there is exactly one Gittins search sequence against $p$. Then for every tie-breaking rule $r\in\mathcal R$ the map
--   $$x\longmapsto f(r,x)=V(\xi(r,x))\in[0,\infty]^n$$
--   is continuous at $p$, as a function on the simplex $\mathcal P$ of hiding strategies.
--
--   Together with Lemma 17 it is used to show that $\bar S(\epsilon)$ is closed.
--
--   **Formalization Note.** Continuity is `ContinuousWithinAt` relative to the simplex, with values in `ℝ≥0∞`ⁿ. A rule `r : ℕ → Equiv.Perm (Fin n)` assigns its ordering to search steps rather than to encountered ties (a disclosed deviation; see the definitions file). $\epsilon<1/n$ is written $\epsilon<1/(n:\mathbb R)$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 42, Lemma 16

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 16, p. 42: at a non-tie point `p ∈ 𝒫(ε)`, for every tie-breaking rule `r`, the map
`x ↦ f(r, x) = V(ξ(r, x))` is continuous at `p` relative to the simplex. -/
theorem lemma_16 {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (ε : ℝ) (hε : 0 < ε) (hεn : ε < 1 / (n : ℝ)) (p : Fin n → ℝ) (hp : p ∈ interiorEps ε)
    (hnt : ¬ IsTiePoint t q p) (r : Rule n) :
    ContinuousWithinAt (ruleVec t q r) (stdSimplex ℝ (Fin n)) p := by sorry

end DiscreteSearchGame.Optimal
