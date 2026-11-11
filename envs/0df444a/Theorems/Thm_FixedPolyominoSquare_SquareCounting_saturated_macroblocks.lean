-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_saturated_macroblocks
-- name    : FixedPolyominoSquare.SquareCounting.saturated_macroblocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:17.365324+00:00
-- url     : https://prove2.me/theorems/8f1df6cb-558d-4d9e-839a-9b69babc454c
-- title:
--   Theorem 6.2 — saturation and rectangular macroblocks
-- statement:
--   Fix integral macrocell parameters $P\geq1$, $c\geq0$, and a positive grid size $n$. The following five assertions hold.
--
--   1. Every component of a saturated spanning index subgraph is a nonempty filled combinatorial rectangle.
--   2. The macrocells are nonempty, pairwise disjoint, and partition $\mathrm{Square}_{Pn+2c}$.
--   3. For any tiling by 4-connected prototiles, all macrocells met by one placement belong to a single component of its actual macrograph.
--   4. Under saturation, the components induce a partition of the physical square into nonempty discrete rectangles. More than one index component yields a rectangular dissection, and every internal adjacency of one component is open.
--   5. If saturation fails in a two-by-two macro-window, every placement meeting the window lies in the closed $\ell_\infty$ neighbourhood of radius $d_T$, the maximum prototile diameter. Those placements determine all four offending edge bits, and
--
--   $$\operatorname{width}(Q_{\rm ext}),\operatorname{height}(Q_{\rm ext})\leq2(P+2c)+2d_T.$$
--
--   This retains the local failure-window assertion as well as the global component statements. The graph and restricted placement set are computed from physical supports.
--
--   Differences from the source:
--   - encoding: integral Pmac at least one, nonnegative integral ccol, positive grid size, graph components and a closed maximum-diameter neighbourhood → natural P,c,n with 1≤P and 1≤n, finite-path components, unordered physical component unions and an explicit closed integer neighbourhood; reason: natural c encodes exactly ccol≥0; equality of the four window edge predicates before and after restricting placements expresses the asserted determination
--   - reading: every prototile is 4-connected (p. 3, a set whose grid-adjacency graph is connected) → FourConnected, which includes nonemptiness; reason: the empty graph is not connected in the standard convention, and the source's prototiles are polyominoes, hence nonempty
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 15, Theorem 6.2; pp. 15–16, standing definitions

import Definitions.Def_FixedPolyominoSquare_SquareCounting_Macrogrid

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Theorem 6.2, p. 15: all five assertions. Parameters are
natural because the source requires integral macrocell coordinates. -/
theorem saturated_macroblocks (P c n : ℕ) (hP : 1 ≤ P) (hn : 1 ≤ n) :
    (∀ E : Finset (Cell × Cell), E ⊆ gridEdges n → Saturated n E →
      ∀ p ∈ square n, FilledRectangle n E (indexComponent n E p)) ∧
    ((∀ p ∈ square n, (macrocell P c n p).Nonempty) ∧
      (∀ p ∈ square n, ∀ q ∈ square n, p ≠ q →
        Disjoint (macrocell P c n p) (macrocell P c n q)) ∧
      (square n).biUnion (macrocell P c n) = square (Lmac P c n)) ∧
    (∀ (T : TileFamily) (pi : Finset (Placement T)),
      (∀ t, FourConnected (T.shape t)) → IsTiling T (square (Lmac P c n)) pi →
      ∀ t ∈ pi, ∃ root ∈ square n, ∀ p ∈ metMacrocells P c n (support T t),
        p ∈ indexComponent n (macroGraph P c n T pi) root) ∧
    (∀ (T : TileFamily) (pi : Finset (Placement T)),
      IsTiling T (square (Lmac P c n)) pi → Saturated n (macroGraph P c n T pi) →
      IsRectangularPartition (square (Lmac P c n))
        (physicalComponents P c n (macroGraph P c n T pi)) ∧
      (2 ≤ (indexComponents n (macroGraph P c n T pi)).card →
        2 ≤ (physicalComponents P c n (macroGraph P c n T pi)).card) ∧
      ∀ root ∈ square n, ∀ e ∈ gridEdges n,
        e.1 ∈ indexComponent n (macroGraph P c n T pi) root →
        e.2 ∈ indexComponent n (macroGraph P c n T pi) root →
        edgePresent (macroGraph P c n T pi) e.1 e.2) ∧
    (∀ (T : TileFamily) (pi : Finset (Placement T)) (p : Cell),
      IsTiling T (square (Lmac P c n)) pi → p ∈ square (n - 1) →
      (∃ i : Fin 4, windowOpen (macroGraph P c n T pi) p i ∧
        windowOpen (macroGraph P c n T pi) p (i + 1) ∧
        ¬ ∀ j, windowOpen (macroGraph P c n T pi) p j) →
      (∀ t ∈ windowPlacements P c n T pi p,
        support T t ⊆ closedNeighbourhood (tileDiameter T) (macroWindow P c n p)) ∧
      (∀ i : Fin 4, windowOpen (macroGraph P c n T pi) p i ↔
        windowOpen (macroGraph P c n T (windowPlacements P c n T pi p)) p i) ∧
      width (closedNeighbourhood (tileDiameter T) (macroWindow P c n p)) ≤
        2 * (P + 2 * c) + 2 * tileDiameter T ∧
      height (closedNeighbourhood (tileDiameter T) (macroWindow P c n p)) ≤
        2 * (P + 2 * c) + 2 * tileDiameter T) := by sorry

end FixedPolyominoSquare.SquareCounting
