-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_corollary_6_19
-- name    : CombOpt.MatchingPolytope.corollary_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:25.150548+00:00
-- url     : https://prove2.me/theorems/4524032d-3418-437f-ab5d-0690cc900ddb
-- title:
--   Corollary 6.19 — every facet needs its own inequality in any defining system
-- statement:
--   Let $P=\{x\in\mathbb R^n:\ A'x=b',\ A''x\le b''\}$ for a finite system of equations and inequalities. Then the system contains a distinct facet-inducing inequality for each facet of $P$: there is an injective map $F\mapsto i(F)$ from the facets of $P$ to the rows of $A''$ such that
--   $$F=\{x\in P:\ (a''_{i(F)})^\top x=b''_{i(F)}\}\quad\text{for every facet } F.$$
--
--   So no linear description of a polyhedron can have fewer inequalities than the polyhedron has facets.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
--
--   Differences from the source:
--   - reading: "any defining system for a polyhedron" → any finite system $A'x=b',\ A''x\le b''$ whose solution set is $P$; reason: the form of defining systems in Theorem 6.17 and in the definition of minimality (p. 212); $A'$ empty gives $Ax\le b$
--   - reading: "a distinct facet-inducing inequality for each of its facets" → an injective assignment of a row of $A''$ inducing it to each facet; reason: distinct facets get distinct inequalities
--   - reading: "the other faces" are proper faces (p. 204) → a proper face is a face different from $\emptyset$ and from $P$; reason: the literal reading of the sentence; with $\emptyset$ proper, $\emptyset$ would be a facet of $\mathbb R^n$ and Corollary 6.19 would fail for the empty system
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Corollary 6.19, p. 213 (PDF p. 221)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsValid
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatchingPolytope_IsProperFace
import Definitions.Def_CombOpt_MatchingPolytope_IsFacet
import Definitions.Def_CombOpt_MatchingPolytope_inducedFace
import Definitions.Def_CombOpt_MatchingPolytope_systemSol

namespace CombOpt.MatchingPolytope

/-- **Corollary 6.19** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Corollary 6.19, p. 213 (PDF p. 221):
"Any defining system for a polyhedron must contain a distinct facet-inducing inequality for each
of its facets."

For any system `A′x = b′, A″x ≤ b″` with solution set `P`, there is an injective assignment
`g` of an inequality `g F` of `A″x ≤ b″` to every facet `F` of `P` such that `g F` induces `F`.

**Formalization Note.** "Defining system" is the form `A′x = b′, A″x ≤ b″` of Theorem 6.17
(`p = 0` gives a pure inequality system `Ax ≤ b`). -/
theorem corollary_6_19 {ι : Type*} [Fintype ι] {p q : ℕ} (A' : Fin p → ι → ℝ)
    (b' : Fin p → ℝ) (A'' : Fin q → ι → ℝ) (b'' : Fin q → ℝ) :
    ∃ g : {F : Set (ι → ℝ) // IsFacet (systemSol A' b' A'' b'') F} → Fin q,
      Function.Injective g ∧
      ∀ F, F.1 = inducedFace (systemSol A' b' A'' b'') (A'' (g F)) (b'' (g F)) := by sorry

end CombOpt.MatchingPolytope
