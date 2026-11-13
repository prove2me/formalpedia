-- Prove2me | Theorems.Thm_DirKECC1549_Main_positive_flow_walk
-- name    : DirKECC1549.Main.positive_flow_walk
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T11:02:34.929886+00:00
-- url     : https://prove2.me/theorems/94342c94-91cb-4b92-90f8-3dbbc8f2f629
-- title:
--   Positive unit flow reaches its sink in its support
-- statement:
--   Let $D$ be a finite directed multigraph with distinct vertices $u,v$, and let $F$ be the support of an integral unit-capacity $u$–$v$ flow of positive value. Then $v$ is reachable from $u$ using only edges in $F$.
--
--   This support-reachability lemma is a step in integral flow decomposition. Edge identifiers distinguish parallel edges, and loops are allowed.
-- source:
--   Reachability step in integral flow decomposition; Ahuja, Magnanti and Orlin, Network Flows (1993), Section 3.5; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9, for the mission graph encoding.

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false

namespace DirKECC1549.Main

theorem positive_flow_walk {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v (q + 1)) :
    ∃ p : List (Fin m), IsWalk D u p v ∧ p.toFinset ⊆ F := by sorry
end DirKECC1549.Main
