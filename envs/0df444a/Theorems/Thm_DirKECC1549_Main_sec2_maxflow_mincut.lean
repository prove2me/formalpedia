-- Prove2me | Theorems.Thm_DirKECC1549_Main_sec2_maxflow_mincut
-- name    : DirKECC1549.Main.sec2_maxflow_mincut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:40.698565+00:00
-- url     : https://prove2.me/theorems/41c2b35b-127b-4517-bf2a-6a87a6e1c3c1
-- title:
--   Section 2, p.9 — λ_D(u,v) is the max-flow and the minimum (u,v)-cut
-- statement:
--   Let $D$ be a directed multigraph and $u\ne v$ vertices. Then $\lambda_D(u,v)$, the maximum number of pairwise edge-disjoint directed $u\to v$ paths, equals the $u\to v$ max-flow with unit capacities, and
--   $$\lambda_D(u,v)=\min_{S:\ (u,v)\text{-cut}}\mathrm{out}_D(S).$$
--   This is the edge version of Menger's theorem; the rest of the mission uses it to pass between path counts and cuts.
--
--   **Formalization Note** The max-flow is the largest value of an integral unit-capacity $u\to v$ flow, given by the set of edges carrying flow $1$; the minimum is taken over all vertex sets $S$ with $u\in S$, $v\notin S$.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and can be deleted from any path, so it changes no out_D, no λ_D and no component; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention; parallel edges are distinct ids, so every count includes multiplicities as on p.9; same instances
--   - encoding: edge-disjoint directed paths; λ_D(u,v) ≥ k → pairwise edge-disjoint trails (walks using no edge id twice); λ ≥ k as "k such trails exist"; reason: edge-disjoint walks shorten to edge-disjoint paths, so the counts agree
--   - encoding: the u → v max-flow → the maximum value of an integral unit-capacity flow, represented by the set of edges carrying flow 1; reason: by the integrality theorem a unit-capacity network has an integral maximum flow; same value
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 2, display after the definition of λ_D, p.9

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3

set_option autoImplicit false

namespace DirKECC1549.Main

/-- §2, p.9 (max-flow/min-cut display): for distinct vertices `u, v` of a directed multigraph,
`λ_D(u, v)` equals the `u → v` max-flow (the largest value of an integral unit-capacity flow) and
`λ_D(u, v) = min_{S : (u,v)-cut} out_D(S)`. -/
theorem sec2_maxflow_mincut {n m : ℕ} (D : Fin m → Fin n × Fin n) (u v : Fin n) (huv : u ≠ v) :
    IsGreatest {q : ℕ | ∃ F : Finset (Fin m), IsUnitFlow D F u v q} (lam D u v) ∧
    IsLeast ((fun S => outCount D S) '' {S : Finset (Fin n) | IsCut S u v}) (lam D u v) := by sorry

end DirKECC1549.Main
