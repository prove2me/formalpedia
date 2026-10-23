-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_lemma_6
-- name    : ApproxOLO.FullInfo.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:43.266408+00:00
-- url     : https://prove2.me/theorems/210185a0-e5b7-421f-9076-5a4e5f39f113
-- title:
--   Lemma 6, p. 11 — if min_i (x − v_i) · w ≤ ε for every unit w, an optimal point p of Problem (5) satisfies ‖p − x‖ ≤ ε
-- statement:
--   Fix $x\in\mathbb R^d$, vectors $v_1,\dots,v_N\in\mathbb R^d$ with $N\ge1$, and $\varepsilon>0$. Suppose that for every Euclidean unit vector $w$,
--   $$\min_{i\in\{1,\dots,N\}}(x-v_i)\cdot w\le\varepsilon .$$
--   Let $(a_1,\dots,a_N)$ be an optimal solution of Problem (5), i.e. a minimizer of $\tfrac12\|\sum_{i=1}^Na_iv_i-x\|^2$ over the probability simplex. Then the point $p=\sum_{i=1}^Na_iv_i$ satisfies
--   $$\|p-x\|\le\varepsilon.$$
--
--   The lemma converts the absence of a separating direction with margin $\varepsilon$ into an explicit convex combination of the $v_i$ that is $\varepsilon$-close to $x$; it is the decomposition half of the separation-or-decomposition procedure (Lemma 5).
--
--   **Formalization Note** $\|\cdot\|$ is Euclidean, and a unit vector is one of Euclidean norm 1. $N\ge1$ is implicit in the page's $\min_{i\in\{1,\dots,N\}}$ and in the simplex constraint of Problem (5).
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, p. 11, Lemma 6 (Problem (5), p. 10)

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Lemma 6, Garber, arXiv:1709.03093v1, p. 11.** Fix `x ∈ ℝ^d`, vectors `v_1, …, v_N ∈ ℝ^d`
(`N ≥ 1`) and `ε > 0`. If for every (Euclidean) unit vector `w`,
`min_{i∈{1,…,N}} (x − v_i) · w ≤ ε`, then for every optimal solution `(a_1, …, a_N)` of
Problem (5) the point `p = Σ_i a_i v_i` satisfies `‖p − x‖ ≤ ε`. -/
theorem lemma_6 {d N : ℕ} (hN : 1 ≤ N) (x : Vec d) (v : Fin N → Vec d) (eps : ℝ)
    (heps : 0 < eps) (hmin : ∀ w : Vec d, euclNorm w = 1 → ∃ i, (x - v i) ⬝ᵥ w ≤ eps)
    (a : Fin N → ℝ) (ha : IsSimplexOpt v x a) :
    euclNorm (∑ i, a i • v i - x) ≤ eps := by sorry

end ApproxOLO.FullInfo
