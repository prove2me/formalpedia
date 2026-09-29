-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
-- name    : AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/efd8707e-8bfb-5e6e-866d-9c41b49102d8
-- title:
--   Openness of the smooth, irreducible, g-dimensional fibre locus
-- statement:
--   Let $S$ be a commutative ring, let $Z$ be a scheme and let $f : Z \to \operatorname{Spec} S$ be a morphism that is proper, flat and locally of finite presentation, and let $g$ be a natural number. Consider the subset of $\operatorname{Spec} S$ consisting of those primes $s$ with the following property: for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ whose kernel is the prime ideal $s$, the second projection $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k \to \operatorname{Spec} k$ of the base change along $\operatorname{Spec}(x)$ is smooth, the scheme $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$ is an irreducible topological space, and its topological Krull dimension equals $g$. The assertion is twofold: this subset is open in $\operatorname{Spec} S$, and for every open subscheme $V$ of $\operatorname{Spec} S$ whose underlying set is contained in that subset, the restriction $f \mid_ V : f^{-1}(V) \to V$ is smooth.
--
--   This is the standard openness statement for the locus of an abelian-scheme-type condition on geometric fibres: the set of points of the base over which all geometric fibres are smooth, irreducible and of dimension $g$ is open, and the morphism is smooth over any open contained in it. It combines openness of the smooth-fibre locus together with the fibrewise criterion for smoothness, local constancy of the number of geometric connected components for proper flat morphisms with geometrically reduced fibres, and semicontinuity of fibre dimension; it is used in the construction of the moduli of framed polarised abelian schemes and in identifying connected components of fibres of prescribed dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} ∧
    ∀ V : (Spec (CommRingCat.of S)).Opens,
      (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} →
      Smooth (f ∣_ V) := by sorry
