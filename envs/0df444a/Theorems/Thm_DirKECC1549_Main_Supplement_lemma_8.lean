-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_lemma_8
-- name    : DirKECC1549.Main.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:20:01.795286+00:00
-- url     : https://prove2.me/theorems/19970a44-304c-488f-8516-4d4ff5cb3dc4
-- title:
--   Lemma 8 — k-blocks survive the split of a candidate
-- statement:
--   Let $G$ be a directed multigraph, $k\ge1$, and $B\subseteq V$ a candidate set. Let $(S,X,T)$ be a partition of $V$ with $|X|<k$, $x\in B\cap S$, $y\in B\cap T$, satisfying the **partition property**: no $u\in S$ is $k$-vertex-connected to any $v\in T$. Put
--   $$L=B\cap S,\quad Z=B\cap X,\quad D=B\setminus(L\cup Z),\quad B_1=L\cup Z,\quad B_2=D\cup Z.$$
--   Then every $k$-block $K$ of $G$ with $K\subseteq B$ satisfies $K\subseteq B_1$ or $K\subseteq B_2$.
--
--   This is the invariant of the recursive $k$-block decomposition: splitting a candidate along a separation loses no $k$-block.
--
--   **Formalization Note** A $k$-block is an inclusion-maximal set of size at least $k$ of pairwise $k$-vertex-connected vertices, maximal in all of $V$.
--
--   Differences from the source:
--   - generalization: directed graph with parallel edges (p.9) → self-loops also allowed; reason: a loop leaves no vertex set and lies on no useful path, so it changes no edge or vertex connectivity; on loop-free multigraphs the statement is exactly the source's
--   - encoding: vertex set V and edge multiset E → vertices Fin n, edge ids Fin m, an edge map Fin m → Fin n × Fin n; reason: Lean convention of the published Graph definition; parallel edges are distinct ids; same instances
--   - encoding: "B1 and B2 obtained from B by the split above" → the split data as hypotheses: B, a partition (S, X, T) of V with |X| < k, x ∈ B ∩ S, y ∈ B ∩ T and the partition property; reason: these are exactly the properties the paper establishes for the split (pp.28–30) before stating the lemma
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Lemma 8, p.30 (the split and the partition property, pp.28–30)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_VertexConn

set_option autoImplicit false

open Finset

namespace DirKECC1549.Main.Supplement

open DirKECC1549.Main

/-- Lemma 8, p.30. Let `B ⊆ V` be a candidate, `(S, X, T)` a partition of `V` with `|X| < k`,
`x ∈ B ∩ S`, `y ∈ B ∩ T`, and the partition property: no `u ∈ S` is `k`-vertex-connected to any
`v ∈ T`. With `L = B ∩ S`, `Z = B ∩ X`, `D = B \ (L ∪ Z)`, `B₁ = L ∪ Z`, `B₂ = D ∪ Z`, every
`k`-block contained in `B` is contained in `B₁` or in `B₂`. -/
theorem lemma_8 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (G : Fin m → Fin n × Fin n)
    (B S X T : Finset (Fin n))
    (hSX : Disjoint S X) (hST : Disjoint S T) (hXT : Disjoint X T) (hcover : S ∪ X ∪ T = univ)
    (hXcard : X.card < k) (x y : Fin n) (hx : x ∈ B ∩ S) (hy : y ∈ B ∩ T)
    (hprop : ∀ u ∈ S, ∀ v ∈ T, ¬ KVertexConnected k G u v)
    (K : Finset (Fin n)) (hK : IsKBlock k G K) (hKB : K ⊆ B) :
    K ⊆ (B ∩ S) ∪ (B ∩ X) ∨ K ⊆ (B \ ((B ∩ S) ∪ (B ∩ X))) ∪ (B ∩ X) := by sorry

end DirKECC1549.Main.Supplement
