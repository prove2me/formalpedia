-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_claim_2
-- name    : DirKECC1549.Main.Supplement.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:21:54.984048+00:00
-- url     : https://prove2.me/theorems/e14214fd-de58-4f8a-bbf2-be667cd8f209
-- title:
--   Claim 2 — in J_k, vertices of U are k-vertex-connected iff they lie in different triples
-- statement:
--   Let $k\ge7$, $\ell=\lfloor (k-1)/3\rfloor$, and let $J_k$ be the graph with a set $U$ of $3\ell$ vertices partitioned into triples $P_0,\dots,P_{\ell-1}$ (every edge between different triples, none inside a triple) and a set $B$ of $h=k+2-3\ell$ pairwise non-adjacent vertices, each adjacent to all of $U$. For distinct $x,y\in U$,
--   $$x,y\ \text{are $k$-vertex-connected in }J_k\iff x\text{ and }y\text{ belong to different triples}.$$
--
--   This describes the $k$-vertex-connectivity relation inside $U$ that the lower-bound construction of Theorem 10 uses.
--
--   **Formalization Note** The vertex $a<3\ell$ of $J_k$ lies in the triple $P_{\lfloor a/3\rfloor}$.
--
--   Differences from the source:
--   - encoding: undirected graph J_k on U ∪ B → SimpleGraph (Fin (k + 2)) with U = {0, …, 3ℓ − 1}, x_{i,j} = 3i + j, and B = {3ℓ, …, k + 1}; reason: a labeling of the k + 2 vertices; same graph
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Claim 2, p.35 (J_k defined on p.35, Figure 3)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_Undirected

set_option autoImplicit false

namespace DirKECC1549.Main.Supplement

/-- Claim 2, p.35: in `J_k` (`k ≥ 7`), two distinct vertices `x, y ∈ U` are `k`-vertex-connected if
and only if they belong to different triples (vertex `a < 3ℓ` lies in the triple `P_{⌊a/3⌋}`). -/
theorem claim_2 (k : ℕ) (hk : 7 ≤ k) (x y : Fin (k + 2))
    (hx : (x : ℕ) < 3 * ell k) (hy : (y : ℕ) < 3 * ell k) (hxy : x ≠ y) :
    UKVertexConnected k (Jk k) x y ↔ (x : ℕ) / 3 ≠ (y : ℕ) / 3 := by sorry

end DirKECC1549.Main.Supplement
