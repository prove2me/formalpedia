-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_semisymmetric_R_L_empty
-- name    : EdgeTransBiCayley.BiDihedrant.semisymmetric_R_L_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:00.563997+00:00
-- url     : https://prove2.me/theorems/068b70e4-2ec7-4453-bd73-46d720daa1d1
-- title:
--   Proof of Theorem 6.1, p. 11 — a connected semisymmetric bi-Cayley graph has R = L = ∅
-- statement:
--   Let $\Gamma = \mathrm{BiCay}(H, R, L, S)$ be a connected bi-Cayley graph over a finite group $H$. If $\Gamma$ is semisymmetric, then
--
--   $$
--   R = L = \emptyset.
--   $$
--
--   Since $\Gamma$ is edge- but not vertex-transitive, it is bipartite with parts the two orbits of $\mathrm{Aut}(\Gamma)$; as $R(H)$ has the orbits $H_0$ and $H_1$, these are the two parts, so there are no edges inside $H_0$ or $H_1$. This is the first step of the proof of Theorem 6.1, reducing the problem to graphs $\mathrm{BiCay}(H, \emptyset, \emptyset, S)$.
--
--   **Formalization Note** Semisymmetry is for the full automorphism group `⊤` of the graph and includes constant valency. The statement is for any finite group $H$, as the paper's argument is.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 11, proof of Theorem 6.1, first two sentences

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem semisymmetric_R_L_empty {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected)
    (hsemi : IsSemisymmetric D.graph) : D.R = ∅ ∧ D.L = ∅ := by sorry

end EdgeTransBiCayley.BiDihedrant
