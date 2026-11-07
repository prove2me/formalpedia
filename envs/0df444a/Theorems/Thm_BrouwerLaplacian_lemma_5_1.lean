-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_5_1
-- name    : BrouwerLaplacian.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:05.676493+00:00
-- url     : https://prove2.me/theorems/4f6225db-3a94-4fb4-9bc8-c5488c5a70d8
-- title:
--   Lemma 5.1 — eigenvalue sums reduce to projections
-- statement:
--   Let $G$ be a simple graph on $[n]$ with $m$ edges and Laplacian $L$, with eigenvalues $\lambda_1(L)\ge\dots\ge\lambda_n(L)$. Fix $1\le k\le n-1$. Suppose that every real $n\times n$ orthogonal projection $P$ of rank $k$ with $P\mathbf 1=0$ satisfies
--
--   $$\sum_{\{i,j\}\in E(G)}\big(P_{ii}+P_{jj}-2P_{ij}-1\big)\le\binom{k+1}{2}.$$
--
--   Then
--
--   $$\sum_{i=1}^k\lambda_i(L)\le m+\binom{k+1}{2}.$$
--
--   This reduces the spectral statement of Brouwer's conjecture to a uniform inequality over projections, which Lemma 5.6 supplies.
--
--   **Formalization Note** Each edge is counted once, as the pair $(i,j)$ with $i<j$ and $i\sim j$. The hypothesis quantifies over all such projections. The eigenvalues are Mathlib's `eigenvalues₀`, sorted non-increasingly and indexed from $0$; $m$ is the number of edges.
--
--   Differences from the source:
--   - encoding: $\sum_{(i,j)\in E(G)}$ → sum over pairs $i<j$ with $i\sim j$; reason: each edge once, as in the paper; same instances
--   - encoding: eigenvalues $\lambda_1\ge\dots\ge\lambda_n$ → `eigenvalues₀` indexed $0,\dots,n-1$; reason: 0-based indexing of the same sorted list
--   - encoding: vertex set $[n]=\{1,\dots,n\}$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.1, pp.4–5

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj

namespace BrouwerLaplacian

open Finset Matrix

/-- **Lemma 5.1 (Eigenvalue Sums Reduce to Projections).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.1, pp.4–5:
"Let G be a graph on n vertices and m edges which has Laplacian L. Fix 1 ≤ k ≤ n − 1. Suppose
that every orthogonal projection P of rank k satisfying P1 = 0 obeys
Σ_{(i,j)∈E(G)} (Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ − 1) ≤ (k+1 choose 2). Then Σᵢ₌₁ᵏ λᵢ(L) ≤ m + (k+1 choose 2)."

**Formalization Note.** Vertices are `Fin n`. The edge sum counts every edge once, as the pair
`(i, j)` with `i < j` and `i ~ j`. The hypothesis is universally quantified over all orthogonal
projections `P` of rank `k` with `P𝟙 = 0`. The eigenvalue sum is over the `k` largest
eigenvalues (`eigenvalues₀`, sorted non-increasingly, indexed from `0`); `m = #G.edgeFinset`. -/
theorem lemma_5_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    (hproj : ∀ P : Matrix (Fin n) (Fin n) ℝ, IsOrthProj P k → P *ᵥ (fun _ => 1) = 0 →
      ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
        ≤ ((k + 1).choose 2 : ℕ)) :
    ∑ i : Fin (Fintype.card (Fin n)) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := by sorry

end BrouwerLaplacian
