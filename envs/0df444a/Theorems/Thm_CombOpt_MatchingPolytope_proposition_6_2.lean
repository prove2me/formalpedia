-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_proposition_6_2
-- name    : CombOpt.MatchingPolytope.proposition_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:21.191509+00:00
-- url     : https://prove2.me/theorems/fc662c23-5ec1-46c3-b160-326e4dbe654c
-- title:
--   Proposition 6.2 — a point outside the convex hull of a finite set is separated by an inequality
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a finite set and let $v\in\mathbb R^n\setminus\operatorname{conv.hull}(S)$. Then there is an inequality $w^\top x\le t$ that separates $v$ from conv.hull$(S)$:
--   $$w^\top s\le t\quad\text{for all } s\in\operatorname{conv.hull}(S),\qquad w^\top v>t.$$
--
--   This separation statement is the tool behind the proofs of Theorems 6.3, 6.10 and 6.11.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
--
--   Differences from the source:
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 6.2, p. 201 (PDF p. 209)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **Proposition 6.2** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 6.2, p. 201 (PDF p. 209):
"Let S ⊆ ℝ^n be a finite set and let v ∈ ℝ^n \ conv.hull(S). Then there exists an inequality
w^T x ≤ t that separates v from conv.hull(S), that is, w^T s ≤ t for all s ∈ conv.hull(S) but
w^T v > t."

**Formalization Note.** `ℝ^n` is `ι → ℝ` for a finite type `ι`; `convexHull ℝ` is the book's
`conv.hull`. -/
theorem proposition_6_2 {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (hS : S.Finite)
    (v : ι → ℝ) (hv : v ∉ convexHull ℝ S) :
    ∃ (w : ι → ℝ) (t : ℝ), (∀ s ∈ convexHull ℝ S, w ⬝ᵥ s ≤ t) ∧ t < w ⬝ᵥ v := by sorry

end CombOpt.MatchingPolytope
