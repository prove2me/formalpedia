-- Prove2me | Theorems.Thm_CircStability_Bondy_theorem_2_1
-- name    : CircStability.Bondy.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:33.612036+00:00
-- url     : https://prove2.me/theorems/533bc0f1-37a7-44f2-bf02-31b7ea0ab520
-- title:
--   Theorem 2.1 (Bondy) — a 2-connected graph in which all but at most one vertex have degree ≥ k has circumference ≥ min{n, 2k}
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and let $k \ge 0$ be an integer. Suppose every vertex of $G$, except for at most one vertex, has degree at least $k$. Then $G$ contains a cycle of length at least $\min\{n,2k\}$, that is,
--
--   $$c(G) \ge \min\{n, 2k\}.$$
--
--   This strengthening of Dirac's theorem, due to Bondy, is a source of long cycles in the proof of the stability theorem.
--
--   **Formalization Note** "Every vertex except at most one" is expressed as: there is a vertex $v_0$ such that every $v \ne v_0$ has degree at least $k$. The conclusion $c(G) \ge m$ is stated as the existence of a cycle of length at least $m$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 7, Theorem 2.1 (Bondy [2])

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem theorem_2_1 (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hdeg : ∃ v₀ : Fin n, ∀ v, v ≠ v₀ → k ≤ G.degree v) :
    ∃ (w : Fin n) (D : G.Walk w w), D.IsCycle ∧ min n (2 * k) ≤ D.length := by sorry
end CircStability.Bondy
