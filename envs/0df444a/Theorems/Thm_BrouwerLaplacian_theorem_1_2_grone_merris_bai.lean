-- Prove2me | Theorems.Thm_BrouwerLaplacian_theorem_1_2_grone_merris_bai
-- name    : BrouwerLaplacian.theorem_1_2_grone_merris_bai
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:07.24768+00:00
-- url     : https://prove2.me/theorems/9f0ac956-72ef-4daf-82db-37f6cd68c941
-- title:
--   Theorem 1.2 (Grone–Merris–Bai) — $\lambda_1+\dots+\lambda_k\le d'_1+\dots+d'_k$
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices, with Laplacian $L=D-A$ and Laplacian eigenvalues $\lambda_1\ge\lambda_2\ge\dots\ge\lambda_n$ counted with multiplicity. Let $d'_j$ be the number of vertices of degree at least $j$ (the conjugate degree sequence). Then for every $1\le k\le n$,
--
--   $$\lambda_1+\dots+\lambda_k\le d'_1+\dots+d'_k.$$
--
--   Together with $\sum_i\lambda_i=2m=\sum_j d'_j$, this says that the Laplacian spectrum is majorized by the conjugate degree sequence (the Grone–Merris conjecture, proved by H. Bai, Trans. Amer. Math. Soc. 363 (2011)). The paper quotes it and uses it for split graphs to prove Lemma 3.2.
--
--   **Formalization Note** The vertex set is an arbitrary finite type. The eigenvalues are Mathlib's `eigenvalues₀` of the symmetric matrix `G.lapMatrix ℝ`, sorted non-increasingly and indexed from $0$, so $\lambda_1+\dots+\lambda_k$ is the sum over indices $<k$.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$ → any finite type $V$ with $n=|V|$; reason: every finite graph is isomorphic to one on $[n]$, and the spectrum and degrees are invariant under relabeling; same instances
--   - encoding: eigenvalues $\lambda_1\ge\dots\ge\lambda_n$ → `eigenvalues₀` indexed $0,\dots,n-1$; reason: 0-based indexing of the same sorted list
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Theorem 1.2, p.2 (cited from H. Bai, Trans. Amer. Math. Soc. 363(8) (2011) 4463–4474)

import Mathlib
import Definitions.Def_BrouwerLaplacian_conjDeg

namespace BrouwerLaplacian

open Finset

/-- **Theorem 1.2 (Grone–Merris–Bai).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Theorem 1.2, p.2:
"The following inequality holds λ₁ + . . . + λₖ ≤ d′₁ + . . . + d′ₖ, for any 1 ≤ k ≤ n."
The paper cites this result; its proof is in H. Bai, *The Grone–Merris conjecture*, Trans. Amer.
Math. Soc. 363(8) (2011), 4463–4474.

For every finite simple graph `G` on `n` vertices and every `1 ≤ k ≤ n`, the sum of the `k`
largest Laplacian eigenvalues is at most `d′₁ + ⋯ + d′ₖ`, where `d′ⱼ` is the number of vertices
of degree at least `j` (Definition 1.1).

**Formalization Note.** `eigenvalues₀` is sorted non-increasingly and indexed from `0`, so
`λ₁ + ⋯ + λₖ` is the sum over indices `< k`. `conjDeg G j = d′ⱼ`, summed over `j = 1, …, k`.
The statement is for all graphs, as printed (the paper uses it only for split graphs). -/
theorem theorem_1_2_grone_merris_bai {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ ∑ j ∈ Icc 1 k, (conjDeg G j : ℝ) := by sorry

end BrouwerLaplacian
