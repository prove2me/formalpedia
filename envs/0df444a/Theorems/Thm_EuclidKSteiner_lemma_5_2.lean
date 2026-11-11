-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_5_2
-- name    : EuclidKSteiner.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:15.362202+00:00
-- url     : https://prove2.me/theorems/b0d1d266-e3fe-4be6-8363-1644af07f90e
-- title:
--   Lemma 5.2 — few prescribed bits give a separating coloring $\chi_x$
-- statement:
--   Let $M$ be a tree on $P$ with nonnegative weights, $n=|P|$, with a heavy child (one with the most leaves) at each internal vertex of $\mathrm{Merge}_M$ and the light edges numbered by distinct positions in $\{1,\dots,n-1\}$. Let $A,B\subseteq P$ be disjoint with $1\le|A\cup B|\le r$. There are disjoint $Z_0,Z_1\subseteq\{0,\dots,n-1\}$ with
--   $$|Z_0|+|Z_1|\le1+r\log_2 n,\qquad |Z_1|\le|A\cup B|,$$
--   such that every string $x$ with $x_j=0$ for $j\in Z_0$ and $x_j=1$ for $j\in Z_1$ produces a coloring $\chi_x$ separating $A$ and $B$, whose stored vertex colors differ across at most $|A\cup B|-1$ edges of $\mathrm{Merge}_M(A\cup B)$.
--
--   Combined with the string families of Corollary 5.4, this gives a small family of colorings separating every relevant pair.
--
--   **Formalization Note** Strings are maps from positions to $\{0,1\}$; only positions $0,\dots,n-1$ are read.
--
--   Differences from the source:
--   - generalization: children ordered by decreasing number of leaves (ties arbitrary), the leftmost heavy, light edges numbered 1, …, n−1 in depth-first order → any heavy-child choice whose heavy child has the largest number of leaves among its siblings, and any injective numbering of the light edges into {1, …, n−1}; reason: the proof uses only that a light step halves the leaf count and that light edges have distinct positions; the page's choices are instances
--   - encoding: strings x ∈ {0,1}^n and log n (base 2) → maps ℕ → Bool (false = 0) of which positions 0, …, n−1 are read; Real.logb 2; reason: footnote 1: all logarithms have base 2
--   - encoding: the merge tree Merge_M recording Kruskal's algorithm and its edges → clusters (singletons and the components of M≤t at edge weights t), each edge named by its child cluster, of length h(parent) − h(child); Merge_M(X) the clusters C ≠ P meeting X; reason: the page identifies each vertex with its cluster
--   - encoding: stored colors computed by the depth-first procedure (c(ρ) = x_0, heavy edges copy, the j-th light edge adds x_j mod 2), each edge colored by its child → storedColor: c(C) = x_0 xor the parity of the number of light clusters D ⊇ C with x_(num D) = 1; chi = storedColor on child clusters; reason: the clusters D ⊇ C are C and its ancestors, so this is the procedure's value unrolled along the root-to-C path
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 5.2, p.21 (PDF p.23); coloring procedure §5.1.1, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_EuclidKSteiner_MergeTree

namespace EuclidKSteiner

/-- **Lemma 5.2.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 5.2, p.21 (PDF p.23):
"Let A, B be disjoint leaf sets of Merge_M with 1 ≤ |A ∪ B| ≤ r. There are disjoint sets
Z_0, Z_1 ⊆ {0, …, n − 1} such that |Z_0| + |Z_1| ≤ 1 + r log n, |Z_1| ≤ |A ∪ B|, and every string x
satisfying x_j = 0 (j ∈ Z_0), x_j = 1 (j ∈ Z_1) produces a coloring χ_x separating A, B. Moreover,
its stored vertex colors differ across at most |A ∪ B| − 1 edges of Merge_M(A ∪ B)."

Let `M` be a tree on `P` (`n = |P|` leaves) with nonnegative weights, fix any heavy-child choice
(each internal vertex of `Merge_M` picks a child with the most descendant leaves) and any numbering of
the light edges by distinct positions in `{1, …, n − 1}`. For all disjoint `A, B ⊆ P` with
`1 ≤ |A ∪ B| ≤ r` there are disjoint `Z₀, Z₁ ⊆ {0, …, n − 1}` with `|Z₀| + |Z₁| ≤ 1 + r log₂ n` and
`|Z₁| ≤ |A ∪ B|` such that every string `x` that is `0` on `Z₀` and `1` on `Z₁` gives a coloring `χ_x`
separating `A` and `B`, whose stored vertex colors differ across at most `|A ∪ B| − 1` edges of
`Merge_M(A ∪ B)`.

**Formalization Note** The page orders children by decreasing number of leaves (ties arbitrary),
calls the leftmost child heavy and numbers the light edges in depth-first order; here every heavy
choice with a child of maximum leaf count and every injective numbering into `{1, …, n − 1}` is
allowed, which contains the page's choices. Strings are maps `ℕ → Bool` (`false` = `0` = red); only
positions `0, …, n − 1` are read. -/
theorem lemma_5_2 {V : Type*} [DecidableEq V] (T : TermTree V) (hv : Finset V → Finset V)
    (hhv : T.IsHeavyChoice hv) (num : Finset V → ℕ) (hnum : T.IsLightNumbering hv num)
    (r : ℕ) (A B : Finset V) (hA : A ⊆ T.P) (hB : B ⊆ T.P) (hAB : Disjoint A B)
    (h1 : 1 ≤ (A ∪ B).card) (hr : (A ∪ B).card ≤ r) :
    ∃ Z₀ Z₁ : Finset ℕ, Z₀ ⊆ Finset.range T.P.card ∧ Z₁ ⊆ Finset.range T.P.card ∧
      Disjoint Z₀ Z₁ ∧
      ((Z₀.card + Z₁.card : ℕ) : ℝ) ≤ 1 + (r : ℝ) * Real.logb 2 (T.P.card : ℝ) ∧
      Z₁.card ≤ (A ∪ B).card ∧
      ∀ x : ℕ → Bool, (∀ j ∈ Z₀, x j = false) → (∀ j ∈ Z₁, x j = true) →
        T.Separates (T.chi hv num x) A B ∧
        ((T.mergeEdges (A ∪ B)).filter (fun C =>
          T.storedColor hv num x C ≠ T.storedColor hv num x (T.parent C))).card ≤
          (A ∪ B).card - 1 := by sorry

end EuclidKSteiner
