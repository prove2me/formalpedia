-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_corollary_1_1
-- name    : BasicPackArb.Main.Supplement.corollary_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:59:47.128067+00:00
-- url     : https://prove2.me/theorems/5cd20f85-8025-4665-8130-ae3e4323b77f
-- title:
--   Corollary 1.1 — an M-connected orientation exists exactly under the partition inequalities
-- statement:
--   Let $G=(V,E)$ be a finite undirected graph with root placement $\pi:S\to V$, and let $M$ be a matroid on $S$. Then
--
--   $$\exists\text{ orientation }D\text{ of }G:\ (D,S,\pi)\text{ is }M\text{-connected}\quad\Longleftrightarrow\quad(G,S,\pi)\text{ is }M\text{-partition-connected}.$$
--
--   Here $M$-connectedness requires $\rho_D(X)+r_M(S_X)\ge r_M(S)$ for every nonempty vertex set $X$, while partition connectedness requires $e_G(\mathcal P)+\sum_{X\in\mathcal P}r_M(S_X)\ge r_M(S)|\mathcal P|$ for every partition into nonempty blocks. No independence condition on $\pi$ is assumed. This corollary supports the undirected packing characterization, Theorem 1.3.
--
--   Differences from the source:
--   - encoding: finite graphs, root sets and matroids on S → finite vertex/root carriers, finite edge sets with edge identities, and M.E = Set.univ; reason: these presentations include every source instance, preserve parallel edges and repeated roots, and express that the ground set is exactly S
--   - encoding: rank differences and partition counts → finite ranks converted from M.eRk and additive inequalities over integers; reason: finite ranks are ordinary natural numbers and integer rearrangement avoids truncated subtraction without changing any case
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 3, Corollary 1.1

import Definitions.Def_BasicPackArb_Main_Supplement_TreePacking

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Corollary 1.1, p. 3: orientation and partition connectedness, with no independence premise. -/
theorem corollary_1_1 {V E S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] [DecidableEq E] (G : Graph V E) (π : S → V)
    (M : Matroid S) (hground : M.E = Set.univ) :
    (∃ σ : E → Bool, MConnected (G.orient σ) π M) ↔
      MPartitionConnected G π M := by sorry

end BasicPackArb.Main.Supplement
