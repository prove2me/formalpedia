-- Prove2me | Theorems.Thm_DynApproxIdx_Main_lemma_7_2
-- name    : DynApproxIdx.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:15.860195+00:00
-- url     : https://prove2.me/theorems/499cc6a9-1b39-4eae-bbdf-f595dd6c740f
-- title:
--   Lemma 7.2 — at most t + k exactly matching sub-pieces of a partition survive k mismatches
-- statement:
--   Let $P=P[0..m)$ and $X=X[0..m)$ be strings of the same length $m$, and let $I_1,\dots,I_t$ be a sorted list of nonempty intervals forming a partition of $[0..m)$. If $k=\delta_H(P,X)<t$, there is a sequence $J_1,\dots,J_w$ of sorted pairwise disjoint intervals such that
--   1. $w\le t+k$, $\ \sum_{j=1}^{w}|J_j|\ge m-k$, and every $J_j$ is contained in some $I_i$;
--   2. $X[J_j]=P[J_j]$ for every $j$;
--   3. $w\ge t-k$, and at least $t-k$ of the intervals $J_1,\dots,J_w$ are among $I_1,\dots,I_t$.
--
--   $$k=\delta_H(P,X)<t\ \Longrightarrow\ \exists\,J_1<\dots<J_w:\ t-k\le w\le t+k,\ \ X[J_j]=P[J_j].$$
--   It is the Hamming counterpart of Lemma 7.1; it says which pieces of a partitioned pattern survive in an approximate occurrence, which the index uses to anchor occurrences.
--
--   Differences from the source:
--
--   - encoding: δ_H(X, Y) = |{i : X[i] ≠ Y[i]}| for equal-length strings (∞ otherwise) → HammingSumset729.Approximation.distance X Y (zip and count mismatches), applied only to equal-length strings; reason: equal on equal lengths; every use here has equal lengths, stated as a hypothesis or forced by the fragment
--   - encoding: intervals [a..b) of integers; |J|, max J + 1 → pairs (a, b) : ℕ × ℕ with a < b; ilen (a, b) = b − a; max J + 1 = J.2; reason: the same nonempty intervals of nonnegative positions
--   - encoding: a sorted list of non-empty intervals I_1, …, I_t that forms a partition of [0..m) → IsSortedPartition m I: nonempty entries, consecutive entries adjacent (I_i.2 = I_{i+1}.1), first starts at 0, last ends at m; reason: a sorted partition into nonempty intervals is exactly such a chain
--   - encoding: sorted pairwise disjoint intervals J_1, …, J_w → IsSortedDisjoint J: nonempty entries with J_j.2 ≤ J_{j+1}.1, i.e. max J_j < min J_{j+1}; reason: the paper's intervals are nonempty (max J_j is used and the proof removes emptied intervals)
--   - encoding: w ≥ t − k and Σ|J_j| ≥ (·) − k; at least t − k of J_1, …, J_w are among I_1, …, I_t → t ≤ w + k and (·) ≤ Σ ilen J_j + k; t ≤ (number of entries of J that are entries of I) + k; reason: the same integer inequalities without natural subtraction; entries of J are pairwise distinct, so counting entries counts intervals
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 30 (PDF 32), Lemma 7.2

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_HammingSumset729_Approximation_Strings
import Definitions.Def_DynApproxIdx_Main_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Lemma 7.2** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 30 (PDF 32)). Let `P = P[0..m)` and `X = X[0..m)` be strings of the same
length `m` and `I_1, …, I_t` a sorted list of nonempty intervals forming a partition of `[0..m)`.
If `k = δ_H(P, X) < t`, there is a sequence of sorted pairwise disjoint intervals `J_1, …, J_w`
such that
(1) `w ≤ t + k`, `Σ_j |J_j| ≥ m − k`, and every `J_j` lies inside some `I_i`;
(2) `X[J_j] = P[J_j]` for every `j`;
(3) `w ≥ t − k`, and at least `t − k` of `J_1, …, J_w` are among `I_1, …, I_t`. -/
theorem lemma_7_2 (P X : List ℕ) (hPX : X.length = P.length) (I : List (ℕ × ℕ)) (k : ℕ)
    (hI : IsSortedPartition P.length I)
    (hk : k = HammingSumset729.Approximation.distance P X) (hkt : k < I.length) :
    ∃ J : List (ℕ × ℕ), IsSortedDisjoint J ∧
      (J.length ≤ I.length + k ∧ P.length ≤ (J.map ilen).sum + k ∧
        ∀ x ∈ J, ∃ y ∈ I, Subinterval x y) ∧
      (∀ x ∈ J, frag X x.1 x.2 = frag P x.1 x.2) ∧
      (I.length ≤ J.length + k ∧ I.length ≤ (J.filter fun x => x ∈ I).length + k) := by sorry

end DynApproxIdx.Main
