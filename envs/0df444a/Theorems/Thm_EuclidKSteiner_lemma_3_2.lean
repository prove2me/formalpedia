-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_3_2
-- name    : EuclidKSteiner.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:54.613127+00:00
-- url     : https://prove2.me/theorems/7ce96abe-b135-42f7-93a2-38779db6a436
-- title:
--   Lemma 3.2 — Euclidean MSTs have degree at most $3^d$; at most $3^d|S|$ Steiner edges
-- statement:
--   1. For every dimension $d$, every finite set $X\subseteq\mathbb R^d$ and every Euclidean minimum spanning tree $T$ of $X$, every point has degree at most $3^d$ in $T$.
--   2. For finite $P,S\subseteq\mathbb R^d$ and every Euclidean minimum spanning tree $T$ of $P\cup S$, at most $3^d\,|S|$ edges of $T$ have an endpoint in $S\setminus P$.
--
--   This is the only geometric fact used by the algorithm: an optimal solution with $k$ candidates has $b=O(k)$ Steiner edges in fixed dimension.
--
--   Differences from the source:
--   - reading: Euclidean minimum spanning trees have bounded degree; a tree with at most k candidates has O(k) Steiner edges → degree at most 3^d, and at most 3^d·|S| edges with an endpoint in S \ P; reason: the explicit constant of the printed proof ('the maximum degree is at most 3^d in dimension d'), which implies the printed bounds
--   - encoding: Steiner edges of an MST on terminals and selected candidates → edges of T with an endpoint in S \ P; reason: an edge touches a selected candidate exactly when it has an endpoint in S that is not a terminal
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidKSteiner_Instance

namespace EuclidKSteiner

open Classical in
/-- **Lemma 3.2.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.2, p.9 (PDF p.11):
"In fixed dimension, Euclidean minimum spanning trees have bounded degree. Hence any such tree with
at most k candidates has O(k) Steiner edges." Proof: "the maximum degree is at most 3^d in
dimension d".

1. For every dimension `d`, every finite point set `X ⊆ ℝ^d` and every Euclidean minimum spanning
   tree `T` of `X`, every point has degree at most `3^d` in `T`.
2. For finite `P, S ⊆ ℝ^d` and every Euclidean minimum spanning tree `T` of `P ∪ S`, at most
   `3^d · |S|` edges of `T` have an endpoint in `S \ P` (the Steiner edges).

**Formalization Note** "Bounded degree" and "O(k)" are stated with the proof's explicit constant
`3^d`. -/
theorem lemma_3_2 :
    (∀ (d : ℕ) (X : Finset (E d)) (T : Finset (Sym2 (E d))), IsEuclMST X T →
      ∀ v : E d, (T.filter (fun e => v ∈ e)).card ≤ 3 ^ d) ∧
    (∀ (d : ℕ) (P S : Finset (E d)) (T : Finset (Sym2 (E d))), IsEuclMST (P ∪ S) T →
      (T.filter (fun e => ∃ v ∈ e, v ∈ S \ P)).card ≤ 3 ^ d * S.card) := by sorry

end EuclidKSteiner
