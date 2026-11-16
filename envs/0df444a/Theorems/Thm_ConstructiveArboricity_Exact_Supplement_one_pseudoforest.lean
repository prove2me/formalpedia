-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_one_pseudoforest
-- name    : ConstructiveArboricity.Exact.Supplement.one_pseudoforest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:16:28.803395+00:00
-- url     : https://prove2.me/theorems/123e217a-c002-4ac7-b52a-960594cdfc64
-- title:
--   Lemma 3.1 — One pseudoforest
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and a supplied $d$-out orientation, where $d\ge1$. Algorithm 2 selects exactly one outgoing edge at every vertex of outdegree $d$ and none at any other vertex. Its selected edges $S$ form a pseudoforest and satisfy
--
--   $$ (d+1)\,\operatorname{cycles}(S)\le n. $$
--
--   One fixed RAM program realizes the specified phase routine on the prepared outgoing adjacency representation in time at most $C(1+n\log(n+2))$, with $C$ independent of the graph, the orientation and $d$. The selected edges are output by identity in a compact list. Preparing the outgoing directory belongs to the outer first stage, whose total time is stated in Lemma 3.2. This result supplies both the exact selection rule and the cycle bound for each descending round.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: asymptotic running times with log n → an additive unit and log(n+2) in the finite-size bounds; reason: totalizes empty and small inputs without changing the asymptotic parameter dependence
--   - encoding: at most n/(d+1) cycles → (d+1) times the integer cycle count is at most n; reason: d is at least one, so this is the identical bound without division
--   - encoding: outgoing adjacency lists used in Algorithm 2 and prepared by the outer stage → the internal input explicitly includes its degree and offset directory; reason: the O(n log n) routine does not include constructing adjacency lists; Lemma 3.2 includes their construction
--   - encoding: unspecified vertex scan and outgoing-edge order in Algorithm 2 → vertices and available outgoing edges are scanned in increasing input identity order; reason: fixes the source algorithm’s permitted choices deterministically; adjacency lists can retain this order under constant-time linked-list deletions
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Lemma 3.1, PDF/printed p.11.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Extraction

namespace ConstructiveArboricity.Exact.Supplement

/-- Lemma 3.1, p.11. Outgoing-list preparation is charged in Lemma 3.2.
One RAM program implements Algorithm 2 on the prepared adjacency directory. -/
theorem one_pseudoforest :
    ∃ (P : Program) (b : ℕ) (C : ℝ), 0 < b ∧ 0 < C ∧
    ∀ (G : Graph) (d : ℕ) (tail : Fin G.m → Fin G.n),
      1 ≤ d → G.IsKOut d tail →
      ∀ W, WidthEnough b (G.n + G.m + d) W →
      ∃ (S : Finset (Fin G.m)) (t : ℕ),
        ExtractResult G tail Finset.univ d S ∧
        (∀ v, (S.filter fun e => tail e = v).card =
          if G.outdegree tail v = d then 1 else 0) ∧
        G.IsPseudoforest (↑S) ∧
        (d + 1) * G.cycleCount (↑S) ≤ G.n ∧
        Runs P (adjacencyInput G tail d) (selectedOutput G S) W t ∧
        (t : ℝ) ≤ C * (1 + G.n * logSize G.n) := by sorry

end ConstructiveArboricity.Exact.Supplement
