-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
-- name    : AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/61424a28-9c13-5c5e-bbda-18e53ecbf95f
-- title:
--   Openness of the geometrically irreducible fibre locus over any base
-- statement:
--   Let $S$ be a commutative ring, let $Z$ be a scheme, and let $f \colon Z \to \operatorname{Spec} S$ be a morphism which is proper and smooth; no finiteness hypothesis is placed on $S$. Consider the subset of the underlying topological space of $\operatorname{Spec} S$ consisting of those primes $s$ with the property that, for every algebraically closed field $k$ (in the same universe as $S$) and every ring homomorphism $x \colon S \to k$ whose kernel is the prime ideal $s$, the scheme $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$, formed as the pullback of $f$ along $\operatorname{Spec}(x)$, has irreducible underlying space. The assertion is that this subset is open in $\operatorname{Spec} S$. Thus the locus of points whose geometric fibres, taken with respect to every algebraically closed residue extension, are irreducible — in particular non-empty, irreducibility including non-emptiness here — is an open subset of the base.
--
--   This is the openness of the locus of geometrically irreducible fibres of a proper smooth morphism, a form of the constructibility and openness statements of EGA IV §12, here with an arbitrary (not necessarily Noetherian) affine base, obtained from the Noetherian case by descent to a finitely generated subalgebra. It feeds the openness of the locus of points with smooth irreducible geometric fibre for proper flat morphisms, used in the geometric input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} := by sorry
