-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_extreme_point_correspondence_v2
-- name    : Disjunctive.ConvexHull.extreme_point_correspondence_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:49.63788+00:00
-- url     : https://prove2.me/theorems/e62f716e-0025-424e-bc53-5aa1cb4923b4
-- title:
--   Corollary 2.2 — extreme points of the lifted polyhedron (corrected)
-- statement:
--   This is Corollary 2.2 of Balas's *Disjunctive Programming*, describing the extreme points of the lifted polyhedron of Theorem 2.1, with its second part corrected.
--
--   Let $P_h := \{x \in \mathbb{R}^n : A_h x \ge b_h\}$ ($h \in Q$), $F := \bigcup_{h\in Q} P_h$, $Q^* := \{h : P_h \ne \emptyset\}$, and let $P$ be the lifted polyhedron of Theorem 2.1: the set of $(x, \{y^h\}_{h\in Q^*}, \{y^h_0\}_{h\in Q^*})$ with
--   $$
--   x = \sum_{h\in Q^*} y^h,\qquad A_h y^h - b_h y^h_0 \ge 0,\quad y^h_0 \ge 0\ (h \in Q^*),\qquad \sum_{h\in Q^*} y^h_0 = 1 .
--   $$
--   1. If $x^*$ is an extreme point of $\mathrm{cl\,conv}(F)$, then for some $k \in Q^*$ the point with $x = x^*$, $(y^k, y^k_0) = (x^*, 1)$ and $(y^h, y^h_0) = (0, 0)$ for $h \ne k$ is an extreme point of $P$.
--   2. Conversely, if $(\bar x, \{\bar y^h\}, \{\bar y^h_0\})$ is an extreme point of $P$, then $\bar y^k = \bar x$ and $\bar y^k_0 = 1$ for some $k \in Q^*$, $(\bar y^h, \bar y^h_0) = (0,0)$ for $h \ne k$, and $\bar x$ is an extreme point of $P_k$.
--
--   **Formalization Note.** The retired version (like the printed corollary, as reproduced in Balas's 2005 survey, Theorem 5.1(ii)) concluded in part 2 that $\bar x$ is an extreme point of $\mathrm{cl\,conv}(F)$. This is false: for $P_0 = \{0\}$ and $P_1 = [-1,1]$ in $\mathbb{R}$, the one-hot lift of $0$ on the disjunct $0$ is an extreme point of $P$, while $0$ is the midpoint of $\pm 1$ in $\mathrm{cl\,conv}(F) = [-1,1]$. The corrected part 2 concludes extremality of $\bar x$ in its own disjunct $P_k$, which is what the lifted structure yields; part 1 is unchanged. The lifted vectors are indexed by all of $Q$ with the entries outside $Q^*$ forced to $0$ (the mission's padding convention for `LiftedPolyhedron`).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §2.1, pp. 19–20, Corollary 2.2 — corrected transcription: in part (ii) the printed 'x̄ is an extreme point of cl conv F' (false) is replaced by 'x̄ is an extreme point of P_k'

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Corollary 2.2 (Balas, *Disjunctive Programming*, Springer 2018, §2.1, pp. 19-20), corrected
in its second part. (i) If `x*` is an extreme point of `cl conv F`, then for some `k ∈ Q*` the
"one-hot" tuple with `(y^k, y^k_0) = (x*, 1)` and `(y^h, y^h_0) = (0, 0)` for `h ≠ k` is an
extreme point of the lifted polyhedron `P` of Theorem 2.1. (ii) Conversely, every extreme point
`(x̄, {ȳ^h, ȳ^h_0})` of `P` is one-hot: `ȳ^k = x̄`, `ȳ^k_0 = 1` for some `k ∈ Q*`,
`(ȳ^h, ȳ^h_0) = (0, 0)` for `h ≠ k`, and `x̄` is an extreme point of `P_k`.

Version 2: the printed (ii) (and the retired statement) concludes that `x̄` is an extreme point
of `cl conv F`, which is false: with `P_0 = {0}` and `P_1 = [-1, 1]` in `ℝ`, the one-hot lift of
`0` on disjunct `0` is extreme in `P`, but `0` is not extreme in `cl conv F = [-1, 1]`. What the
lifted structure does give is extremality of `x̄` in its own disjunct `P_k`. -/
theorem extreme_point_correspondence_v2 {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    (∀ xstar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet m A b))),
      ∃ k ∈ FeasibleIndices m A b, ∃ y : Q → Fin n → ℝ, ∃ y0 : Q → ℝ,
        (xstar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) ∧
        y k = xstar ∧ y0 k = 1 ∧ ∀ h, h ≠ k → y h = 0 ∧ y0 h = 0)
    ∧
    (∀ (xbar : Fin n → ℝ) (y : Q → Fin n → ℝ) (y0 : Q → ℝ),
      (xbar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) →
      ∃ k ∈ FeasibleIndices m A b, y k = xbar ∧ y0 k = 1 ∧ (∀ h, h ≠ k → y h = 0 ∧ y0 h = 0) ∧
        xbar ∈ Set.extremePoints ℝ (Poly (A k) (b k))) := by sorry

end Disjunctive.ConvexHull
