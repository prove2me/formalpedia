-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_minimal_counterexample_edge_matching
-- name    : CorrColoring.ThreeChoosable.minimal_counterexample_edge_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:05:15.05798+00:00
-- url     : https://prove2.me/theorems/03184d5d-5554-4951-b6e9-51a72c4ceaf1
-- title:
--   Lemma 10 — in a minimal counterexample, $|E(C_{uv})| \ge 2$ off $S$, and full off triangles
-- statement:
--   Let $B = (G, S, C, \varphi_0)$ be a minimal counterexample (a target admitting no $C$-coloring that extends $\varphi_0$, with $s(B)$ lexicographically minimum). If $e = uv$ is an edge of $G$ that does not join two vertices of $S$, then
--
--   $$|E(C_{uv})| \ge 2,$$
--
--   and if moreover $e$ lies in no triangle of $G$, then $e$ is full in $C$.
--
--   This is the first step of the reduction: in a minimal counterexample the correspondences are as dense as the constraints permit.
--
--   **Formalization Note** $|E(C_{uv})|$ is the number of colour pairs $(c,d)$ with $(u,c)(v,d) \in E(C_{uv})$. "Not contained in a triangle" is: no vertex $w$ is adjacent to both $u$ and $v$. As in the paper, the hypothesis describes a hypothetical object: once Theorem 8 is proved, no minimal counterexample exists.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 14, Lemma 10

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_Target
import Definitions.Def_CorrColoring_ThreeChoosable_Straight

namespace CorrColoring.ThreeChoosable

/-- Lemma 10 (Dvořák–Postle, p. 14). -/
theorem minimal_counterexample_edge_matching (B : Target) (hB : B.IsMinimalCounterexample)
    (u v : B.V) (huv : B.G.Adj u v) (hS : ¬ (u ∈ B.S ∧ v ∈ B.S)) :
    2 ≤ Nat.card {p : Fin 3 × Fin 3 // B.C.M u p.1 v p.2} ∧
      ((¬ ∃ w, B.G.Adj u w ∧ B.G.Adj v w) → Full B.C u v) := by sorry

end CorrColoring.ThreeChoosable
