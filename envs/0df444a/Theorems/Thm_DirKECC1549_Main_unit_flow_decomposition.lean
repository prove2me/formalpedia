-- Prove2me | Theorems.Thm_DirKECC1549_Main_unit_flow_decomposition
-- name    : DirKECC1549.Main.unit_flow_decomposition
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:24:46.328199+00:00
-- url     : https://prove2.me/theorems/23cac4cb-e1dd-4622-8341-fc60dc652d8b
-- title:
--   Unit-flow decomposition into edge-disjoint trails
-- statement:
--   Let $D$ be a finite directed multigraph with distinct vertices $u,v$ and let $q\ge0$. There are $q$ pairwise edge-disjoint directed trails from $u$ to $v$ if and only if there is an integral unit-capacity $u$–$v$ flow of value $q$.
--
--   Flows are represented by the set of edges carrying one unit. Parallel edges have distinct identifiers and loops are allowed; any circulation components need not appear in the trails.
-- source:
--   Flow decomposition theorem; Ahuja, Magnanti and Orlin, Network Flows (1993), Section 3.5; see also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem unit_flow_decomposition {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) :
    HasDisjointPaths D q u v ↔ ∃ F : Finset (Fin m), IsUnitFlow D F u v q := by sorry
end DirKECC1549.Main
