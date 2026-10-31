-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_proposition_6_1
-- name    : CombOpt.MatchingPolytope.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:16.835024+00:00
-- url     : https://prove2.me/theorems/6d362930-d0c7-4eab-9128-18229b2fad10
-- title:
--   Proposition 6.1 — a linear function has the same maximum on a finite set and on its convex hull
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a finite nonempty set and let $w\in\mathbb R^n$. Then
--   $$\max\{w^\top x:\ x\in S\}=\max\{w^\top x:\ x\in\operatorname{conv.hull}(S)\},$$
--   and both maxima are attained.
--
--   Optimizing a linear objective over a finite combinatorial set is thus a linear program over its convex hull, which is how the chapter turns combinatorial problems into polyhedral ones.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The statement asserts a number $m$ that is the greatest value of $w^\top x$ both on $S$ and on conv.hull$(S)$.
--
--   Differences from the source:
--   - encoding: $\max$ over a finite set $S$ (undefined for $S=\emptyset$) → hypothesis $S\neq\emptyset$ and a common greatest value $m$ (`IsGreatest`) of both sets; reason: the book's maxima exist only for nonempty $S$; the hypothesis excludes only the undefined case
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 6.1, p. 200 (PDF p. 208)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **Proposition 6.1** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 6.1, p. 200 (PDF p. 208):
"Let S ⊆ ℝ^n be a finite set and let w ∈ ℝ^n. Then
max{w^T x : x ∈ S} = max{w^T x : x ∈ conv.hull(S)}."

**Formalization Note.** Both maxima exist and are equal: some `m` is the greatest value of
`w^T x` on `S` and on `conv.hull(S)`. `S` is nonempty: for `S = ∅` neither maximum is defined.
`convexHull ℝ` is the set of convex combinations, the book's `conv.hull` for a finite set. -/
theorem proposition_6_1 {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (hS : S.Finite)
    (hne : S.Nonempty) (w : ι → ℝ) :
    ∃ m : ℝ, IsGreatest ((fun x => w ⬝ᵥ x) '' S) m ∧
      IsGreatest ((fun x => w ⬝ᵥ x) '' convexHull ℝ S) m := by sorry

end CombOpt.MatchingPolytope
