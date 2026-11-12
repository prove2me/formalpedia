-- Prove2me | Theorems.Thm_DirKECC1549_Main_claim_1
-- name    : DirKECC1549.Main.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:23.790183+00:00
-- url     : https://prove2.me/theorems/8e5e3768-43d4-48d5-9f6e-d19ecfd8529c
-- title:
--   Claim 1 — k-edge-connectivity is decided inside strongly connected components
-- statement:
--   Let $G$ be a directed multigraph, $k\ge1$, and $u,v$ any vertices. Then $u\leftrightarrow^G_k v$ if and only if $u$ and $v$ are strongly connected and $u\leftrightarrow^{G[S]}_k v$, where $S$ is their strongly connected component and $G[S]$ the induced subgraph.
--
--   This justifies the recursion of Algorithm 3, line 4, on the strongly connected components.
--
--   **Formalization Note** $G[S]$ has its vertices renamed $0,\dots,|S|-1$ in increasing order; the second condition reads $k$-edge-connectivity of the renamed copies of $u$ and $v$ in $G[S]$.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and can be deleted from any path, so it changes no out_D, no λ_D and no component; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention; parallel edges are distinct ids, so every count includes multiplicities as on p.9; same instances
--   - encoding: edge-disjoint directed paths; λ_D(u,v) ≥ k → pairwise edge-disjoint trails (walks using no edge id twice); λ ≥ k as "k such trails exist"; reason: edge-disjoint walks shorten to edge-disjoint paths, so the counts agree
--   - reading: "for any u, v" with the k of Algorithm 3 → k ≥ 1; reason: the claim is used for k ≥ 1 (Algorithm 3's range); at k = 0 it is false: in the graph with two vertices and no edges, u ↔_0 v holds but u, v are not strongly connected
--   - encoding: the induced subgraph of their strongly connected component → G[S] with vertices renamed 0, …, |S|−1 in increasing order and its edges in increasing id order; reason: Lean convention for a subgraph as a graph on Fin |S|; same instances
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Claim 1 (in the proof of Lemma 4), p.17

import Mathlib
import Definitions.Def_DirKECC1549_Main_Graph

set_option autoImplicit false

namespace DirKECC1549.Main

/-- Claim 1, p.17: for `k ≥ 1` and any vertices `u, v`, `u, v` are `k`-edge-connected in `G`
iff they are strongly connected and `k`-edge-connected in the induced subgraph `G[S]` of their
strongly connected component `S`. -/
theorem claim_1 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (G : Fin m → Fin n × Fin n) (u v : Fin n) :
    KEdgeConnected k G u v ↔
      StronglyConn G u v ∧
        liftRel (sccOf G u) (KEdgeConnected k (induced G (sccOf G u))) u v := by sorry

end DirKECC1549.Main
