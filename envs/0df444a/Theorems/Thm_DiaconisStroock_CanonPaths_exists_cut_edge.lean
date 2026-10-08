-- Prove2me | Theorems.Thm_DiaconisStroock_CanonPaths_exists_cut_edge
-- name    : DiaconisStroock.CanonPaths.exists_cut_edge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:18.483504+00:00
-- url     : https://prove2.me/theorems/6b0d0ee8-299e-4027-a964-0b3a296adb6e
-- title:
--   §3B: a walk from S to its complement crosses the cut
-- statement:
--   Let $S$ be a set of states. Any finite vertex list beginning at $x\in S$ and ending at $y\notin S$ contains a consecutive directed edge $(u,v)$ with $u\in S$ and $v\notin S$:
--
--   $$
--   x\in S,\quad y\notin S,\quad \gamma:x\leadsto y
--   \quad\Longrightarrow\quad
--   \exists (u,v)\in\gamma:\ u\in S,\ v\notin S.
--   $$
--
--   This elementary crossing fact identifies the path weights counted in the cut argument of Proposition 7.
--
--   **Formalization Note** The claim only uses the first and last vertices of the list. It does not require every step to have positive transition probability.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 54, §3B, proof of Proposition 7; https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.CanonPaths

/-- A walk beginning inside a cut and ending outside traverses an oriented cut edge
(§3B, proof of Proposition 7, p. 54). -/
theorem exists_cut_edge {V : Type*} [DecidableEq V] (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∉ S) (p : List V)
    (hp : p.head? = some x) (hp' : p.getLast? = some y) :
    ∃ e ∈ DiaconisStroock.Poincare.pathEdges p, e.1 ∈ S ∧ e.2 ∉ S := by sorry

end DiaconisStroock.CanonPaths
