-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_8
-- name    : CompactRouting.Labeled.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:44.651275+00:00
-- url     : https://prove2.me/theorems/ff99f871-42bf-4d3b-893e-9b97e05ab311
-- title:
--   Lemma 8 — every vertex of a cluster tree stores its own tree label
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. For any tree labels $L(x,T(C(w)))$ and the routing tables $RT$ of §4.1: for every $w\in V$ and every vertex $z$ of the cluster tree $T(C(w))$ (whose vertex set is $C(w)$),
--   $$\langle\mathrm{id}(w),\,L(z,T(C(w)))\rangle\ \text{is an entry of the bunch part of } RT(z),$$
--   so $L(z,T(C(w)))\in RT(z)$. This guarantees the return label needed by Algorithm 1.
--
--   Differences from the source:
--   - reading: 'every vertex z of T(C(w))' → z ∈ C(w); reason: §2.1 (p. 6): T(C(w)) has vertex set C(w); the tree itself is not constructed
--   - encoding: 'L(z, T(C(w))) ∈ RT(z)' → the pair (id(w), L(z, T(C(w)))) is an entry of the bunch part of RT(z); reason: the proof's reading: the label is in the first part, keyed by id(w)
--   - generalization: the tree labels of Lemma 4 and the paper's pivots → any tree labels `tl` and any pivot map `p`; reason: the bunch part of RT(z) depends on neither; specializes to the paper's
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 12, Lemma 8

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_Tables

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 12, Lemma 8:
"For every w ∈ V and every vertex z of T(C(w)), L(z, T(C(w))) ∈ RT(z)."
The vertex set of `T(C(w))` is `C(w)` (§2.1, p. 6); `tl w z` is the tree label
`L(z, T(C(w)))`, and the conclusion says that it is stored in the first (bunch) part of `RT(z)`
under the key `id(w)`. -/
theorem lemma_8 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n)
    (tl : Fin G.n → Fin G.n → List Bool) :
    ∀ w z : Fin G.n, z ∈ cluster A w → (vid w, tl w z) ∈ (tableOf A p tl z).bunchPart := by sorry

end CompactRouting.Labeled
