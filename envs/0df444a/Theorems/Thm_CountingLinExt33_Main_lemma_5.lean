-- Prove2me | Theorems.Thm_CountingLinExt33_Main_lemma_5
-- name    : CountingLinExt33.Main.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:08.731377+00:00
-- url     : https://prove2.me/theorems/852f8201-967b-40e1-b9d1-af4f3a67b0e6
-- title:
--   Lemma 5 — correctness of the weighted deadline DP
-- statement:
--   Let $P$ be a finite poset on $n$ elements, $B$ any antichain, and $g$ any compatible earliest-successor pattern. Let $P_g$ be the augmented transitive closure, $X=V\setminus B$, and use the initial state, terminal state and weighted transitions defined above. If $W_l$ is the total weight of terminal paths of length $l$, then
--
--   $$W_l=0\quad(l\ne n),\qquad W_n=e(P_g).$$
--
--   Thus the total weight of all paths from $(\varnothing,(A_c(\varnothing))_c)$ to $(X,0)$ equals $e(P_g)$. Each path contributes the product of its edge weights, including the multiplicity $q_c$ of an antichain move. This is the correctness statement used to combine the pattern contributions.
--
--   **Formalization Note** The any-antichain scope is stated explicitly at the opening of §4. The empty path has weight one. All core predecessors and deadlines are constructed from the source relations rather than arbitrary supplied constraints.
--
--   Differences from the source:
--   - encoding: a finite vertex set → Fin n, with n = 0 allowed; reason: every finite set can be relabeled without changing its relations or cardinalities
--   - encoding: deadlines in Y together with infinity → Option (Fin n), padded by zero coordinates outside Y; reason: a distinct sentinel represents infinity and unreachable dummy coordinates change no path
--   - encoding: nonnegative availability counts → availability coordinates in Fin (n+1); reason: every reachable coordinate is at most the n antichain elements; the invariant remains to be proved
--   - encoding: the weight of all complete paths → the n-step weighted sum and a conclusion that every other length has weight zero; reason: no complete path is dropped and the empty input is included
-- source:
--   Keigo Oka, STOC 2027 submission #725 (October 2026), printed p. 5 (PDF p. 6), Lemma 5; printed p. 7 (PDF p. 8), §4 explicit extension to any antichain

import Definitions.Def_CountingLinExt33_Main_Orders

namespace CountingLinExt33.Main

/-- Keigo Oka, STOC 2027 submission #725 (October 2026), printed p.5 / PDF p.6, Lemma 5,
with the explicit any-antichain extension on printed p.7 / PDF p.8, Section 4.
The length clause ensures no complete weighted paths are omitted by the n-step sum. -/
theorem lemma_5 (n : ℕ) (P : PartialOrder (Fin n)) (B : Finset (Fin n))
    (hB : Antichain P B) (g : Fin n → Option (Fin n)) (hg : Compatible P B g) :
    (∀ l : ℕ, l ≠ n → dpPaths P B g hg l (dpTerminal B) = 0) ∧
      dpPaths P B g hg n (dpTerminal B) = extensionCount (patternOrder P B g hg) := by sorry

end CountingLinExt33.Main
