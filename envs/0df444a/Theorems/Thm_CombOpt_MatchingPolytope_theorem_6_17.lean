-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_17
-- name    : CombOpt.MatchingPolytope.theorem_6_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:18.175546+00:00
-- url     : https://prove2.me/theorems/f2cb5c6e-3b99-4c83-b51d-03ecaca8b82d
-- title:
--   Theorem 6.17 — minimal defining systems: independent equations, one facet per inequality
-- statement:
--   Let $P=\{x\in\mathbb R^n:\ A'x=b',\ A''x\le b''\}$ be a nonempty polyhedron, where $A'$ and $A''$ have finitely many rows. Then the defining system is minimal if and only if
--
--   1. the rows of $A'$ are linearly independent, and
--   2. for each row $i$ of $A''$ the inequality $(a''_i)^\top x\le b''_i$ induces a facet of $P$, and distinct rows of $A''$ induce distinct facets.
--
--   This identifies the irredundant linear descriptions of a polyhedron with its facets.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. Linear independence is of the family of rows, so a repeated row is dependent.
--
--   Differences from the source:
--   - reading: "induces a distinct facet of $P$" → each row of $A''$ induces a facet, and the map from rows to induced faces is injective; reason: "distinct" refers to different rows inducing different facets, as the proof (p. 213, "$F_i$ is distinct from the facets corresponding to other rows") shows
--   - reading: "the other faces" are proper faces (p. 204) → a proper face is a face different from $\emptyset$ and from $P$; reason: the literal reading of the sentence; with $\emptyset$ proper, $\emptyset$ would be a facet of $\mathbb R^n$ and Corollary 6.19 would fail for the empty system
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.17, p. 213 (PDF p. 221)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsValid
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatchingPolytope_IsProperFace
import Definitions.Def_CombOpt_MatchingPolytope_IsFacet
import Definitions.Def_CombOpt_MatchingPolytope_inducedFace
import Definitions.Def_CombOpt_MatchingPolytope_systemSol
import Definitions.Def_CombOpt_MatchingPolytope_IsMinimalSystem

namespace CombOpt.MatchingPolytope

/-- **Theorem 6.17** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.17, p. 213 (PDF p. 221):
"Let P = {x ∈ ℝ^n : A′x = b′, A″x ≤ b″} be a nonempty polyhedron. Then the defining system is
minimal if and only if the rows of A′ are linearly independent and for each row i of A″ the
inequality (a″_i)^T x ≤ b″_i induces a distinct facet of P."

**Formalization Note.** `A′` has rows `A' j` (`j : Fin p`), `A″` rows `A'' i` (`i : Fin q`).
"Linearly independent rows" is `LinearIndependent ℝ A'` (a repeated row is dependent). "Induces a
distinct facet" is: each row induces a facet, and different rows induce different facets. -/
theorem theorem_6_17 {ι : Type*} [Fintype ι] {p q : ℕ} (A' : Fin p → ι → ℝ) (b' : Fin p → ℝ)
    (A'' : Fin q → ι → ℝ) (b'' : Fin q → ℝ) (hne : (systemSol A' b' A'' b'').Nonempty) :
    IsMinimalSystem A' b' A'' b'' ↔
      LinearIndependent ℝ A' ∧
      (∀ i : Fin q, IsFacet (systemSol A' b' A'' b'')
        (inducedFace (systemSol A' b' A'' b'') (A'' i) (b'' i))) ∧
      Function.Injective (fun i : Fin q =>
        inducedFace (systemSol A' b' A'' b'') (A'' i) (b'' i)) := by sorry

end CombOpt.MatchingPolytope
