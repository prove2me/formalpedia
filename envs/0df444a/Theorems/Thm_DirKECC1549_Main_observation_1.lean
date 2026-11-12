-- Prove2me | Theorems.Thm_DirKECC1549_Main_observation_1
-- name    : DirKECC1549.Main.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:24.28182+00:00
-- url     : https://prove2.me/theorems/efacee36-a510-4b3f-aaf3-10655f5df42f
-- title:
--   Observation 1 — (k, Δ)-connectivity is an equivalence relation
-- statement:
--   Let $G$ be a directed multigraph and $k,\Delta\ge0$ integers. Call $u,v$ $(k,\Delta)$-connected if no $(<k)$-out set $S$ ($\emptyset\ne S\subsetneq V$, $\mathrm{out}_D(S)<k$) with $\mathrm{vol}_D(S)\le\Delta$, for any $D\in\{G,G^R\}$, contains exactly one of $u,v$. Then $(k,\Delta)$-connectivity is an equivalence relation on $V(G)$.
--
--   Lemma 1 refines each $(k-1)$-edge-connected component into these classes.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and can be deleted from any path, so it changes no out_D, no λ_D and no component; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention; parallel edges are distinct ids, so every count includes multiplicities as on p.9; same instances
--   - generalization: k ≥ 2 and Δ ≥ k − 1 (standing in §3.1) → all integers k, Δ ≥ 0; reason: the observation holds for every k, Δ and specializes to the source's range
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.1, Definition 1 and Observation 1, p.11

import Mathlib
import Definitions.Def_DirKECC1549_Main_Graph

set_option autoImplicit false

namespace DirKECC1549.Main

/-- Observation 1, p.11: `(k, Δ)`-connectivity is an equivalence relation on `V(G)`. -/
theorem observation_1 {n m : ℕ} (k Δ : ℕ) (G : Fin m → Fin n × Fin n) :
    Equivalence (KDeltaConnected k Δ G) := by sorry

end DirKECC1549.Main
