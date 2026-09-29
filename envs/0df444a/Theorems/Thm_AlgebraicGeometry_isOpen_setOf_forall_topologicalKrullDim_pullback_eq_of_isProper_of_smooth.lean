-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
-- name    : AlgebraicGeometry.isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/e535eeb4-783f-549b-b861-e570b7602233
-- title:
--   Openness of the locus of geometric fibres of given dimension
-- statement:
--   Let $S$ be a commutative ring, let $Z$ be a scheme, and let $f : Z \to \operatorname{Spec} S$ be a morphism of schemes that is proper and smooth (both as typeclass hypotheses). Assume that for every algebraically closed field $k$ (in the same universe as $S$ and $Z$) and every ring homomorphism $x : S \to k$, the scheme $\operatorname{pullback} f\,(\operatorname{Spec} x)$ — the geometric fibre of $f$ at the geometric point determined by $x$ — has irreducible underlying topological space, this irreducibility being required at all such $k$ and $x$, not only at those lying over a prescribed point. Let $g$ be a natural number. Then the set of those points $s$ of the underlying topological space of $\operatorname{Spec} S$ with the property that for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ whose kernel is the prime ideal corresponding to $s$, the topological Krull dimension of the geometric fibre $\operatorname{pullback} f\,(\operatorname{Spec} x)$ equals $g$ (as an element of $\mathbb{N}_\infty$ with a bottom element adjoined), is open in $\operatorname{Spec} S$.
--
--   This is the openness, on the base, of the locus where the geometric fibres of a proper smooth morphism with irreducible geometric fibres have a prescribed dimension, a form of the standard semicontinuity results for fibre dimension (EGA IV 13.1.3). It feeds into [`AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat`](thm.html#AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat), in the analysis of the geometry of the relevant families of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f]
    (hirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} := by sorry
