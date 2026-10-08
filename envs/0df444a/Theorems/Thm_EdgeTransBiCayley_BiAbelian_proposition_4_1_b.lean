-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiAbelian_proposition_4_1_b
-- name    : EdgeTransBiCayley.BiAbelian.proposition_4_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:29.103993+00:00
-- url     : https://prove2.me/theorems/4ffd00ff-5adb-4087-8100-155583f2d51f
-- title:
--   Proposition 4.1(b) — edge transitivity implies vertex transitivity
-- statement:
--   Let $\Gamma=\operatorname{BiCay}(H,R,L,S)$ be connected, with $H$ finite and abelian. If the full graph automorphism group acts transitively on undirected edges, then it acts transitively on vertices:
--
--   $$
--   \Gamma\text{ edge transitive}\quad\Longrightarrow\quad\Gamma\text{ vertex transitive}.
--   $$
--
--   This is the corrected first assertion of Proposition 1.3 and rules out connected semisymmetric bi-Cayley graphs over abelian groups.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 6, Proposition 4.1(b)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- Proposition 4.1(b), p. 6. -/
theorem proposition_4_1_b {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected)
    (hedge : IsEdgeTransitive D.graph) :
    IsVertexTransitive D.graph := by sorry
end EdgeTransBiCayley.BiAbelian
