-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_proposition_6_16
-- name    : CombOpt.MatchingPolytope.proposition_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:11.935992+00:00
-- url     : https://prove2.me/theorems/d78c84e8-3d7c-4167-9caa-102f36593f37
-- title:
--   Proposition 6.16 — a nonempty proper face is a facet iff it has dimension one less
-- statement:
--   Let $P\subseteq\mathbb R^n$ be a polyhedron and $F$ a nonempty proper face of $P$. Then
--   $$F \text{ is a facet of } P \iff \dim(F)=\dim(P)-1.$$
--
--   This is the usual way of recognizing facets in practice: one exhibits $\dim(P)$ affinely independent points on the face.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. Dimensions are integers.
--
--   Differences from the source:
--   - reading: "the other faces" are proper faces (p. 204) → a proper face is a face different from $\emptyset$ and from $P$; reason: the literal reading of the sentence; with $\emptyset$ proper, $\emptyset$ would be a facet of $\mathbb R^n$ and Corollary 6.19 would fail for the empty system
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 6.16, p. 212 (PDF p. 220)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_CombOpt_MatchingPolytope_IsValid
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatchingPolytope_IsProperFace
import Definitions.Def_CombOpt_MatchingPolytope_IsFacet
import Definitions.Def_CombOpt_MatchingPolytope_AffinelyIndependent
import Definitions.Def_CombOpt_MatchingPolytope_dim

namespace CombOpt.MatchingPolytope

/-- **Proposition 6.16** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 6.16, p. 212 (PDF p. 220):
"Let F be a nonempty proper face of a polyhedron P. Then F is a facet if and only if
dim(F) = dim(P) − 1."

**Formalization Note.** `IsProperFace P F` already includes `F ≠ ∅`. Dimensions are integers. -/
theorem proposition_6_16 {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) (hP : IsPolyhedron P)
    (hF : IsProperFace P F) :
    IsFacet P F ↔ dim F = dim P - 1 := by sorry

end CombOpt.MatchingPolytope
