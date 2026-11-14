-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_two_vertex_bridge
-- name    : ConsistentSubmodular.Objective.two_vertex_bridge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:46.494197+00:00
-- url     : https://prove2.me/theorems/f853d4ac-58f4-4b70-81ad-7e337b0e185a
-- title:
--   Two-vertex bridge — every point on an edge of the simplex has value at least $\tfrac34 V$
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on the ground set $\{0,\dots,m\}$ of candidate indices, and let $a\neq b$ be two indices. Let $V\ge 0$ satisfy $V\le f(\{a\})$ and $V\le f(\{b\})$. For every $x\in[0,1]$, let $p_x=(1-x)\,\delta_a+x\,\delta_b$ be the point of the segment from the vertex $\delta_a$ to the vertex $\delta_b$, and let $\mathbb E_{I\sim p_x}$ denote expectation over the random set $I$ containing each index $i$ independently with probability $p_x(i)$ (so $I$ contains $a$ with probability $1-x$, $b$ with probability $x$, and no other index). Then
--   $$\mathbb E_{I\sim p_x}\bigl[f(I)\bigr]\;\ge\;\frac34\,V .$$
--
--   This is the two-candidate special case of the edge bound of the two-type interpolation lemma (Lemma B.3, with $Q=\emptyset$). It shows that a segment joining two vertices of value at least $V$ is uniformly safe at level $3/4$, which is what the bridge between two cores in the deterministic certificate construction requires.
--
--   **Formalization Note**: the expectation is `finiteExpectation`, the sum over all subsets of Bernoulli weights, and `f.value` is evaluated on subsets of `Fin (m+1)`; the value $f(\emptyset)$ need not vanish.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/Bridge.lean#L18-L48 (`ConsistentSubmodular.Objective.two_vertex_bridge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {m n : ℕ}

theorem ConsistentSubmodular.Objective.two_vertex_bridge (f : Objective (m + 1)) (a b : Fin (m + 1)) (hab : a ≠ b)
    (V : ℝ) (hV : 0 ≤ V) (ha : V ≤ f.value {a}) (hb : V ≤ f.value {b})
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (3 : ℝ) / 4 * V ≤ finiteExpectation (mix (vertex a) (vertex b) x) f.value := by sorry
