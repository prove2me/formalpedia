-- Prove2me | Theorems.Thm_BrouwerLaplacian_theorem_3_1_brouwer
-- name    : BrouwerLaplacian.theorem_3_1_brouwer
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:58:34.677898+00:00
-- url     : https://prove2.me/theorems/22b7a1fe-7907-4652-8014-00bc63d3fb19
-- title:
--   Theorem 3.1 (Brouwer's conjecture) — $\lambda_1+\dots+\lambda_k\le m+\binom{k+1}{2}$
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices with $m$ edges, let $L=D-A$ be its Laplacian ($D$ the diagonal degree matrix, $A$ the adjacency matrix), and let $\lambda_1\ge\lambda_2\ge\dots\ge\lambda_n\ge 0$ be the eigenvalues of $L$, counted with multiplicity. Then for every $1\le k\le n$,
--
--   $$\lambda_1+\dots+\lambda_k\le m+\binom{k+1}{2}.$$
--
--   This is Brouwer's Laplacian conjecture, here proved for every graph and every $k$. The bound is exact for some graphs (for instance the complete graph at $k = n-1$), and it complements the Grone–Merris–Bai majorization bound by a bound depending only on the number of edges.
--
--   **Formalization Note** The vertex set is an arbitrary finite type. The eigenvalues are Mathlib's `eigenvalues₀` of the symmetric matrix `G.lapMatrix ℝ` (equal to $D-A$), sorted non-increasingly and indexed from $0$, so $\lambda_1+\dots+\lambda_k$ is the sum over indices $<k$. $m$ is the number of edges, and $\binom{k+1}{2}$ is the natural number `(k + 1).choose 2`.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$ → any finite type $V$ with $n=|V|$; reason: every finite graph is isomorphic to one on $[n]$, and the spectrum and edge count are invariant under relabeling; same instances
--   - encoding: eigenvalues $\lambda_1\ge\dots\ge\lambda_n$ → `eigenvalues₀` indexed $0,\dots,n-1$; reason: 0-based indexing of the same sorted list
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Theorem 3.1, p.2 (proof §5, pp.4–8)

import Mathlib

namespace BrouwerLaplacian

open Finset

/-- **Theorem 3.1 (Brouwer's Conjecture).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Theorem 3.1, p.2:
"For any graph G with Laplacian eigenvalues λ₁ ≥ λ₂ ≥ · · · λₙ ≥ 0, we have:
λ₁ + . . . + λₖ ≤ m + (k+1 choose 2), for any 1 ≤ k ≤ n."

For every finite simple graph `G` on `n = |V|` vertices with `m` edges and every `1 ≤ k ≤ n`,
the sum of the `k` largest eigenvalues of the Laplacian `L = D − A` (counted with
multiplicity) is at most `m + (k+1 choose 2)`.

**Formalization Note.** `G.lapMatrix ℝ` is Mathlib's `degMatrix − adjMatrix`, the paper's
`L = D − A` (§1, p.1). `eigenvalues₀` lists the eigenvalues of the symmetric matrix `L`, with
multiplicity, in non-increasing order indexed by `Fin n` from `0`, so the paper's `λᵢ` is
`eigenvalues₀ ⟨i − 1, _⟩` and `λ₁ + ⋯ + λₖ` is the sum over indices `< k`. `m` is the number
of edges `#G.edgeFinset`, and `(k+1 choose 2)` is `(k + 1).choose 2`. The vertex type is any
finite type (the paper's `[n]` is `Fin n`). -/
theorem theorem_3_1_brouwer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := by sorry

end BrouwerLaplacian
