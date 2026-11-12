-- Prove2me | Theorems.Thm_DirKECC1549_Main_lemma_4
-- name    : DirKECC1549.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:53.912073+00:00
-- url     : https://prove2.me/theorems/2fe2436e-c106-4b06-8ddb-4f6a04e7b029
-- title:
--   Lemma 4 — Algorithm 3 returns P_k(G)
-- statement:
--   Let $G$ be a directed multigraph and $k\ge1$. For every run of Algorithm 3, $\mathrm{kEdgeConnectedComponents}(G,k)$, its output $P$ is $P_k(G)$: two vertices lie in the same block of $P$ if and only if they are $k$-edge-connected in $G$.
--
--   This is the correctness half of Theorem 1.
--
--   **Formalization Note** Algorithm 3 is the run relation of the definitions: every choice of root, every output of Lemmas 1 and 2 meeting their guarantees, and every residual graph of a value-$q$ integral flow is allowed, so the statement covers all executions.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and can be deleted from any path, so it changes no out_D, no λ_D and no component; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention; parallel edges are distinct ids, so every count includes multiplicities as on p.9; same instances
--   - encoding: edge-disjoint directed paths; λ_D(u,v) ≥ k → pairwise edge-disjoint trails (walks using no edge id twice); λ ≥ k as "k such trails exist"; reason: edge-disjoint walks shorten to edge-disjoint paths, so the counts agree
--   - generalization: the outputs of Algorithm 3 → the outputs of every run of the run relation: any root, any outputs meeting the guarantees of Lemmas 1 and 2, and the residual graph of any integral unit flow of value q; reason: every execution of Algorithm 3 is such a run (Ford–Fulkerson's reversed edges form an integral flow of value q), so the statement specializes to the source's
--   - reading: Algorithm 3 with parameter k → k ≥ 1; reason: the algorithm's input range (Theorem 1, k ≥ 1; base case k = 1, p.17)
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 and Lemma 4, p.17

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3

set_option autoImplicit false

namespace DirKECC1549.Main

/-- Lemma 4, p.17: for every `k ≥ 1`, every output `P` of every run of Algorithm 3 on a multigraph
`G` is `P_k(G)`: two vertices lie in the same block of `P` iff they are `k`-edge-connected. -/
theorem lemma_4 {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ) (hk : 1 ≤ k)
    (P : Fin n → Fin n → Prop) (hrun : Alg3Run n m G k P) :
    ∀ u v, P u v ↔ KEdgeConnected k G u v := by sorry

end DirKECC1549.Main
