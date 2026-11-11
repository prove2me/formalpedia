-- Prove2me | Theorems.Thm_DynApproxIdx_Main_lemma_7_1
-- name    : DynApproxIdx.Main.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:19.675247+00:00
-- url     : https://prove2.me/theorems/ffa536cb-1dc8-4b39-a808-2a254fb4cdd6
-- title:
--   Lemma 7.1 — an optimal edit transformation leaves at most t + k exactly aligned sub-pieces of a partition, splitting its cost
-- statement:
--   Let $P=P[0..m)$ and $X$ be strings and $I_1,\dots,I_t$ a sorted list of nonempty intervals forming a partition of $[0..m)$. If $k=\delta_E(P,X)<t$, there are sequences of sorted pairwise disjoint intervals $J_1,\dots,J_w$ (positions of $P$) and $J'_1,\dots,J'_w$ (positions of $X$) such that
--   1. $w\le t+k$, $\ \sum_{j=1}^{w}|J_j|\ge\max(m,|X|)-k$, and every $J_j$ is contained in some $I_i$;
--   2. $X[J'_j]=P[J_j]$ for every $j$;
--   3. $w\ge t-k$, and at least $t-k$ of the intervals $J_1,\dots,J_w$ are among $I_1,\dots,I_t$;
--   4. for every $j$ and every $q\in[0..|J_j|)$, with $r=\max J_j+1$ and $r'=\max J'_j+1$,
--   $$\delta_E\bigl(P[0..r-q),X[0..r'-q)\bigr)+\delta_E\bigl(P[r-q..m),X[r'-q..|X|)\bigr)=k.$$
--
--   The lemma describes the pieces of a partitioned pattern that an optimal alignment preserves, and how the alignment splits at each of them; the index anchors $k$-edit occurrences at these pieces.
--
--   Differences from the source:
--
--   - encoding: strings over the integer alphabet Σ, 0-based positions; δ_E the minimum number of insertions, deletions and substitutions → List ℕ; PMEdits.Main.ed, the minimum cost of an alignment-graph path from (0,0) to (|U|,|V|); reason: the standard bijection between edit sequences and alignment-graph paths; same values
--   - encoding: intervals [a..b) of integers; |J|, max J + 1 → pairs (a, b) : ℕ × ℕ with a < b; ilen (a, b) = b − a; max J + 1 = J.2; reason: the same nonempty intervals of nonnegative positions
--   - encoding: a sorted list of non-empty intervals I_1, …, I_t that forms a partition of [0..m) → IsSortedPartition m I: nonempty entries, consecutive entries adjacent (I_i.2 = I_{i+1}.1), first starts at 0, last ends at m; reason: a sorted partition into nonempty intervals is exactly such a chain
--   - encoding: sorted pairwise disjoint intervals J_1, …, J_w → IsSortedDisjoint J: nonempty entries with J_j.2 ≤ J_{j+1}.1, i.e. max J_j < min J_{j+1}; reason: the paper's intervals are nonempty (max J_j is used and the proof removes emptied intervals)
--   - encoding: w ≥ t − k and Σ|J_j| ≥ (·) − k; at least t − k of J_1, …, J_w are among I_1, …, I_t → t ≤ w + k and (·) ≤ Σ ilen J_j + k; t ≤ (number of entries of J that are entries of I) + k; reason: the same integer inequalities without natural subtraction; entries of J are pairwise distinct, so counting entries counts intervals
--   - encoding: X[J′_j] for intervals J′_j of positions of X → J′_j ⊆ [0..|X|) stated as a conclusion clause (J′_j.2 ≤ |X|), and J, J′ lists of the same length w; reason: the notation X[J′_j] is defined only for such intervals; J_j ⊆ [0..m) already follows from J_j ⊆ I_i
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 28 (PDF 30), Lemma 7.1

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Lemma 7.1** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 28 (PDF 30)). Let `P = P[0..m)` and `X` be strings and `I_1, …, I_t` a sorted
list of nonempty intervals forming a partition of `[0..m)`. If `k = δ_E(P, X) < t`, there are
sequences of sorted pairwise disjoint intervals `J_1, …, J_w` (of positions of `P`) and
`J′_1, …, J′_w` (of positions of `X`) such that
(1) `w ≤ t + k`, `Σ_j |J_j| ≥ max(m, |X|) − k`, and every `J_j` lies inside some `I_i`;
(2) `X[J′_j] = P[J_j]` for every `j`;
(3) `w ≥ t − k`, and at least `t − k` of `J_1, …, J_w` are among `I_1, …, I_t`;
(4) for every `j` and `q ∈ [0..|J_j|)`, with `r = max J_j + 1` and `r′ = max J′_j + 1`,
`δ_E(P[0..r−q), X[0..r′−q)) + δ_E(P[r−q..m), X[r′−q..|X|)) = k`. -/
theorem lemma_7_1 (P X : List ℕ) (I : List (ℕ × ℕ)) (k : ℕ)
    (hI : IsSortedPartition P.length I) (hk : k = ed P X) (hkt : k < I.length) :
    ∃ J J' : List (ℕ × ℕ), J.length = J'.length ∧ IsSortedDisjoint J ∧ IsSortedDisjoint J' ∧
      (∀ x ∈ J', x.2 ≤ X.length) ∧
      (J.length ≤ I.length + k ∧ max P.length X.length ≤ (J.map ilen).sum + k ∧
        ∀ x ∈ J, ∃ y ∈ I, Subinterval x y) ∧
      (∀ (j : ℕ) (hj : j < J.length) (hj' : j < J'.length),
        frag X J'[j].1 J'[j].2 = frag P J[j].1 J[j].2) ∧
      (I.length ≤ J.length + k ∧ I.length ≤ (J.filter fun x => x ∈ I).length + k) ∧
      ∀ (j : ℕ) (hj : j < J.length) (hj' : j < J'.length) (q : ℕ), q < ilen J[j] →
        ed (frag P 0 (J[j].2 - q)) (frag X 0 (J'[j].2 - q)) +
          ed (frag P (J[j].2 - q) P.length) (frag X (J'[j].2 - q) X.length) = k := by sorry

end DynApproxIdx.Main
