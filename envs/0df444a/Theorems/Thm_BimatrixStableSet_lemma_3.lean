-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_3
-- name    : BimatrixStableSet.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:46.244089+00:00
-- url     : https://prove2.me/theorems/b5f63e71-7919-42e4-bca1-8a4afea1f07f
-- title:
--   Lemma 3 — non-degeneracy, label counts, and simplicity of $P,Q$
-- statement:
--   Let $(A,B)$ be an $m\times n$ bimatrix game with best-response polytopes $P$ and $Q$. The following are equivalent:
--
--   1. the game is non-degenerate;
--   2. no point in $P$ has more than $m$ labels and no point in $Q$ has more than $n$ labels;
--   3. $P$ and $Q$ are simple polytopes, and for both polytopes any redundant inequality is never binding.
--
--   Furthermore, assume that the game is non-degenerate and that $(x,y)\in P\times Q$ is an equilibrium. Then $x$ is a vertex of $P$, $y$ is a vertex of $Q$, $x$ has exactly $m$ labels, and $y$ has exactly the other $n$ labels.
--
--   This lemma puts non-degeneracy into polyhedral form, so that equilibria become vertex pairs.
--
--   Differences from the source:
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
--   - reading: "exactly the other $n$ labels" → $|\mathrm{labels}(y)|=n$ and the label sets of $x$ and $y$ are disjoint; reason: "the other" means the labels not at $x$
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 3, p.7

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse

namespace BimatrixStableSet

variable {m n : ℕ}

/-- Lemma 3, p.7 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): for a bimatrix game `(A, B)`
with best-response polytopes `P` and `Q`, the following are equivalent:
(a) the game is non-degenerate;
(b) no point in `P` has more than `m` labels and no point in `Q` has more than `n` labels;
(c) `P` and `Q` are simple polytopes, and for both polytopes any redundant inequality is never
binding.
Furthermore, if the game is non-degenerate and `(x, y) ∈ P × Q` is an equilibrium, then
(d) `x` is a vertex of `P`, `y` is a vertex of `Q`, `x` has exactly `m` labels and `y` has exactly
the other `n` labels.

**Formalization Note.** "The other `n` labels" is the disjointness of the two label sets. Label sets
are subsets of the finite type `Fin m ⊕ Fin n`, so `ncard` is the true count. -/
theorem lemma_3 (A B : Matrix (Fin m) (Fin n) ℝ) (hPQ : HasBestResponsePolytopes A B) :
    (IsNondegenerate A B ↔
      (∀ x ∈ (bestResponseP B).carrier, ((bestResponseP B).labels x).ncard ≤ m) ∧
      (∀ y ∈ (bestResponseQ A).carrier, ((bestResponseQ A).labels y).ncard ≤ n)) ∧
    (IsNondegenerate A B ↔
      ((bestResponseP B).IsSimple (bestResponseP B).carrier ∧
        ∀ k, (bestResponseP B).IsRedundant k →
          ∀ x ∈ (bestResponseP B).carrier, ¬ (bestResponseP B).IsBinding x k) ∧
      ((bestResponseQ A).IsSimple (bestResponseQ A).carrier ∧
        ∀ k, (bestResponseQ A).IsRedundant k →
          ∀ y ∈ (bestResponseQ A).carrier, ¬ (bestResponseQ A).IsBinding y k)) ∧
    (IsNondegenerate A B → ∀ x y, IsEquilibrium A B x y →
      x ∈ (bestResponseP B).vertices (bestResponseP B).carrier ∧
      y ∈ (bestResponseQ A).vertices (bestResponseQ A).carrier ∧
      ((bestResponseP B).labels x).ncard = m ∧
      ((bestResponseQ A).labels y).ncard = n ∧
      Disjoint ((bestResponseP B).labels x) ((bestResponseQ A).labels y)) := by sorry

end BimatrixStableSet
