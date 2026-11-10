-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_21
-- name    : DistancePreserver934.Exact.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:48.486197+00:00
-- url     : https://prove2.me/theorems/6370a22c-6b02-4123-bbbd-b6861a9762b7
-- title:
--   Lemma 21 (removing a covered demand set)
-- statement:
--   Let $R$ be a demand set of $K$, $K$ a minimal distance preserver of $(K,R)$ with at most $n$ vertices, and suppose a nonempty $S\subseteq V(K)$ covers a nonempty $Q\subseteq R$ with $\operatorname{diam}_K(S)<\infty$. There is an absolute constant $A>0$ and a distance preserver $H(Q)\subseteq K$ of $(K,Q)$ such that, for **every** distance preserver $K'\subseteq K$ of $(K,R\setminus Q)$,
--   $$|E(K)|-|E(K')|\le|E(H(Q))|\le A\left(n+\sqrt{n\,|Q|\,|S|\,\operatorname{diam}_K(S)}\right).\tag{28}$$
--
--   One $H(Q)$ works for all residual preservers $K'$. Lemma 24 combines this with Equation (36) to bound each Step 2 loss.
--
--   Differences from the source:
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 21, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 21 (removing a covered demand set), printed p.21 / PDF p.22.  Let `K` be a minimal
distance preserver of `(K, R)` with at most `n` vertices, and let a nonempty `S ⊆ V(K)` cover a
nonempty `Q ⊆ R` with `diam_K(S) < ∞`.  There is a distance preserver `H(Q) ⊆ K` of `(K, Q)`
such that for every distance preserver `K' ⊆ K` of `(K, R \ Q)`,
`|E(K)| − |E(K')| ≤ |E(H(Q))| ≤ A (n + √(n |Q| |S| diam_K(S)))` (Equation (28)), `A` absolute. -/
theorem lemma_21 : ∃ A : ℝ, 0 < A ∧
    ∀ (V : Type) [Fintype V] (K : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ)
      (S : Finset V) (Q : Finset (Sym2 V)),
      IsDemandSet K R → IsMinimalPreserver K K R → Fintype.card V ≤ n →
      S.Nonempty → Q.Nonempty → Q ⊆ R → Covers K S Q → diam K S ≠ ⊤ →
      ∃ HQ : SimpleGraph V, IsPreserver K HQ Q ∧
        (∀ K' : SimpleGraph V, IsPreserver K K' (R \ Q) →
          (numEdges K : ℝ) - (numEdges K' : ℝ) ≤ (numEdges HQ : ℝ)) ∧
        (numEdges HQ : ℝ) ≤ A * ((n : ℝ) +
          Real.sqrt ((n : ℝ) * (Q.card : ℝ) * (S.card : ℝ) * ((diam K S).toNat : ℝ))) := by sorry

end DistancePreserver934.Exact
