-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_Supplement_bounded_geometric_sufficiency
-- name    : AlgebraicFPT.HittingSet.Supplement.bounded_geometric_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:42:59.237555+00:00
-- url     : https://prove2.me/theorems/8cbc0a4a-437f-4cfe-93f9-079b523d4fda
-- title:
--   Theorem 5.1 — Bounded geometric sufficiency
-- statement:
--   Let $G$ be any finite simple undirected graph with $n$ vertices, let $1\le h\le k$ be natural numbers, and let $s,v$ be vertices. Write $\mathcal P_{h,s,v}$ for the full family of ordered simple $h$-vertex paths from $s$ to $v$, and $V(P)$ for a path's support. There exists a single subfamily $R\subseteq\mathcal P_{h,s,v}$ such that
--
--   $$|R|\le B(h,k-h)=\sum_{j=0}^{k-h}h^j.$$
--
--   For every vertex set $Q$ of cardinality at most $k-h$, that same $R$ satisfies
--
--   $$\bigl(\exists P\in R:\,V(P)\cap Q=\varnothing\bigr)\iff\bigl(\exists P\in\mathcal P_{h,s,v}:\,V(P)\cap Q=\varnothing\bigr).$$
--
--   Define $L_S=\{z\in\mathbb Q^n:\forall x\in S,\ z_x=0\}$, $Y=\bigcup_{P\in R}L_{V(P)}$, $X=\bigcup_{P\in\mathcal P_{h,s,v}}L_{V(P)}$, and let $\mathbf1_Q$ be the rational indicator point. For every such query,
--
--   $$\mathbf1_Q\in Y\iff\mathbf1_Q\in X,\qquad \operatorname{codim}L_{V(P)}=h\quad(P\in R).$$
--
--   This preserves precisely the avoidance information needed for later extensions; it does not assert equality of $X$ and $Y$. Empty full path families are included, and queries may contain either endpoint.
--
--   **Formalization Note** Codimension means a finite Krull dimension $r$ satisfying $r+h=n$, computed from the actual rational coordinate-space point set. Every subspace's dimension assertion is a conclusion, never a premise. The bound is exactly the source's sum, with no asymptotic constants.
--
--   Differences from the source:
--   - encoding: finite simple undirected graph with labelled vertices → Mathlib SimpleGraph on Fin n with decidable adjacency; reason: finite relabelling and decidability add no mathematical restriction; n may be zero
--   - encoding: ordered simple h-vertex paths and the sum B(h,k−h) → finite families of length-h vertex lists and an inclusive Finset.range(k−h+1) sum; reason: all orders and all j=0 through k−h terms are retained; h≤k prevents truncation
--   - encoding: rational coordinate subspaces of codimension h → published zeroSet over ℚ and a finite algDim value r with r+h=n; reason: the actual rational point sets and Krull dimension express geometric codimension without a numerical label
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), p.11, Theorem 5.1 (Bounded geometric sufficiency); proof p.20, Appendix D

import Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Geometry

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet.Supplement

/-- Theorem 5.1, p.11; Appendix D, p.20. One subfamily is chosen before every query.
Its rational coordinate-space union preserves indicator membership, and each retained
space has actual codimension h. Empty full families are permitted. -/
theorem bounded_geometric_sufficiency {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k h : ℕ) (hh : 1 ≤ h) (hhk : h ≤ k) (s v : Fin n) :
    ∃ R : Finset (List (Fin n)),
      R ⊆ pathFamily G h s v ∧
      R.card ≤ representativeBound h (k - h) ∧
      (∀ Q : Finset (Fin n), Q.card ≤ k - h →
        (AvoidsQuery R Q ↔ AvoidsQuery (pathFamily G h s v) Q) ∧
        (indicator Q ∈ familyLocus R ↔ indicator Q ∈ familyLocus (pathFamily G h s v))) ∧
      (∀ P ∈ R, HasCodimension (coordinateSpace (support P)) h) := by sorry

end AlgebraicFPT.HittingSet.Supplement
