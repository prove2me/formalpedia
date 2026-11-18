-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_small_hitting_count
-- name    : AlgebraicFPT.HittingSet.small_hitting_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:11:18.278057+00:00
-- url     : https://prove2.me/theorems/140473ed-3041-41af-8b76-ab26048d9dc4
-- title:
--   Cumulative count of minimal bounded-rank hitting sets
-- statement:
--   Let $E$ be a finite hypergraph on $n\ge0$ vertices, and let $k\ge0$ and $d\ge1$ be natural numbers. Suppose that every edge has at most $d$ vertices. The entire collection $\mathcal H_{\le k}(E)$ of inclusion-minimal hitting sets of size at most $k$ satisfies
--
--   $$
--   \#\mathcal H_{\le k}(E)\le d^k.
--   $$
--
--   The bound is independent of the number of vertices. It is the cumulative estimate derived immediately before Theorem 3.2, and implies the printed bound on minimal hitting sets of size exactly $k$. Empty families and empty hyperedges are allowed.
--
--   **Formalization Note** The cardinality is an extended natural, so the finite upper bound also asserts finiteness.
-- source:
--   Liming Cai and Sixiang Zhang, Toward Algebraic Geometry of Fixed-Parameter Tractability: Case Studies, STOC 2027 submission #1035, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1035.pdf, §3.1, p.5, cumulative estimate immediately before Theorem 3.2 (positive d as in Lemma 3.1).

import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets

set_option autoImplicit false

theorem AlgebraicFPT.HittingSet.small_hitting_count (n : ℕ) (E : Finset (Finset (Fin n))) (k d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ E, e.card ≤ d) :
    (AlgebraicFPT.HittingSet.smallHittingSets E k).encard ≤ (d ^ k : ℕ) := by sorry
