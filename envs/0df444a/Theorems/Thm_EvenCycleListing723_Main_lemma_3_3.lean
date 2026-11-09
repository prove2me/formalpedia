-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_lemma_3_3
-- name    : EvenCycleListing723.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:07.760769+00:00
-- url     : https://prove2.me/theorems/307d006a-eef8-47a0-9aa5-73c6f7dfd429
-- title:
--   Lemma 3.3 — local tree-layer cycle count
-- statement:
--   Let $h,k$ be positive integers with $h\le k-1$, let $G$ be a finite simple undirected graph, and let $T$ be a tree subgraph of depth exactly $h$ rooted at $u$. Write $L_i$ for the vertices at distance $i$ from $u$ in $T$. Let $R$ be disjoint from every vertex of $T$, and include all ambient edges between $L_h$ and $R$ in a bipartite graph $F$. Write $d_L=|E(F)|/|L_h|$ and $d_R=|E(F)|/|R|$. If both averages are at least $16k^2$, then some integer $j\in\{0,\ldots,h\}$ satisfies
--
--   $$\#\{C_{2k}\text{ copies in }G\text{ meeting }L_j\}\ \ge\ \alpha_k|L_h|d_L(d_Ld_R)^{k-h+j-1},\qquad \alpha_k=2^{-6k}(2k)^{-(2k-2)}.$$
--
--   This counts distinct whole cycles, not pairs consisting of a cycle and a vertex. The tree need not be induced or a BFS tree. The positive thresholds force both denominators to be nonzero. This local result is the counting ingredient for the degree-weighted bound. The source attributes it to Jiang–Yepremyan, Lemma 5.4; the statement here is audited against this submission's Lemma 3.3.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), or Fin m with m ≤ n; reason: every finite vertex set can be relabeled; SimpleGraph imposes precisely simplicity and undirectedness
--   - encoding: unoriented noninduced cycle copies → edge sets of simple closed walks, with canonical dihedral vertex lists for output; reason: rotation and reversal identify the same copy; different cyclic edge orders remain distinct and chords are allowed
--   - encoding: tree of depth h in G with layers L_j and all edges F between L_h and R → a connected acyclic tree on a vertex subtype, with tree distances and real averages of the complete cross-edge set; reason: the tree need not be induced or BFS; disjointness is from every tree vertex, and positive thresholds exclude zero denominators
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), p.6, Lemma 3.3 (Jiang–Yepremyan [JY20, Lemma 5.4]); canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_GraphModel

set_option autoImplicit false

namespace EvenCycleListing723.Main

/-- Lemma 3.3, p.6, including the exact constant and the tree's own layers. -/
theorem lemma_3_3 (n h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k - 1)
    (G : SimpleGraph (Fin n)) (T : RootedTreeIn G) (hdepth : treeDepth T h)
    (R : Finset (Fin n)) (hR : Disjoint R T.vertices)
    (hdL : 16 * (k : ℝ) ^ 2 ≤ averageLeft G (treeLayer T h) R)
    (hdR : 16 * (k : ℝ) ^ 2 ≤ averageRight G (treeLayer T h) R) :
    ∃ j : ℕ, j ≤ h ∧
      alpha k * (treeLayer T h).card * averageLeft G (treeLayer T h) R *
        (averageLeft G (treeLayer T h) R * averageRight G (treeLayer T h) R) ^
          (k - h + j - 1) ≤ (copiesMeeting G k (treeLayer T j) : ℝ) := by sorry

end EvenCycleListing723.Main
