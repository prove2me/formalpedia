-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiAbelian_semisymmetric_R_L_empty
-- name    : EdgeTransBiCayley.BiAbelian.semisymmetric_R_L_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:38.191775+00:00
-- url     : https://prove2.me/theorems/69c278c8-d59b-46be-84a7-ac27e23e3e22
-- title:
--   Proof of Proposition 4.1(b) — the two fibres form the bipartition
-- statement:
--   Let $\Gamma=\operatorname{BiCay}(H,R,L,S)$ be a connected edge-transitive graph over a finite group $H$. If $\Gamma$ is not vertex transitive, its two vertex orbits give a bipartition; the two copies $H_0$ and $H_1$ are its parts. Consequently there are no edges inside either copy:
--
--   $$
--   R=L=\varnothing.
--   $$
--
--   This is the group-independent step in the proof of Proposition 4.1(b). It reduces the edge-transitive abelian case to Proposition 4.1(a).
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 6, proof of Proposition 4.1(b), bipartition step

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- The bipartition step in the proof of Proposition 4.1(b), p. 6. -/
theorem semisymmetric_R_L_empty {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected)
    (hedge : IsEdgeTransitive D.graph)
    (hnotvertex : ¬ IsVertexTransitive D.graph) :
    D.R = ∅ ∧ D.L = ∅ := by sorry
end EdgeTransBiCayley.BiAbelian
