-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback
-- name    : AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/043f8fc8-5e0f-5268-8236-7370f5a888a7
-- title:
--   Base change of a closed immersion into a fibre product
-- statement:
--   Let $g : G \to S$ be a morphism of schemes, let $R$, $k$, $L$, $A$ be commutative rings with $k$ and $L$ given as $R$-algebras, and let $s_R : \operatorname{Spec} R \to S$ be a morphism. Let $\iota : \operatorname{Spec} L \to G$ satisfy $\iota$ followed by $g$ equal to $\operatorname{Spec}(\mathrm{algebraMap}\,R\,L)$ followed by $s_R$, and assume the induced morphism $\operatorname{Spec} L \to G \times_S \operatorname{Spec} R$ obtained from this commuting square, namely `pullback.lift`, is a closed immersion. Let $s : \operatorname{Spec} k \to S$ be a morphism assumed equal to $\operatorname{Spec}(\mathrm{algebraMap}\,R\,k)$ followed by $s_R$. Let $a : L \to A$ and $c : k \to A$ be ring homomorphisms such that the square formed by $\operatorname{Spec} a$, $\operatorname{Spec} c$, $\operatorname{Spec}(\mathrm{algebraMap}\,R\,L)$ and $\operatorname{Spec}(\mathrm{algebraMap}\,R\,k)$ is cartesian (so $\operatorname{Spec} A$ is $\operatorname{Spec} L \times_{\operatorname{Spec} R} \operatorname{Spec} k$), and assume the square expressing that $\operatorname{Spec} a$ followed by $\iota$ followed by $g$ equals $\operatorname{Spec} c$ followed by $s$ commutes. Then the morphism $\operatorname{Spec} A \to G \times_S \operatorname{Spec} k$ induced by $\operatorname{Spec} a$ followed by $\iota$ and by $\operatorname{Spec} c$ is a closed immersion.
--
--   This is the stability of closed immersions under base change, packaged in the form in which the two relevant morphisms are presented as lifts into fibre products over $S$: a closed subscheme of $G \times_S \operatorname{Spec} R$ cut out by a point with values in $L$ stays closed after passing to $k$-coefficients. It is used in the construction of the Néron-type object attached to a modular curve at $p$, where a monomorphism into a fibre product is needed after base change along an ordinary idempotent bridge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback
    {G S : Scheme.{u}} (g : G ⟶ S)
    {R k L A : Type u} [CommRing R] [CommRing k] [CommRing L] [CommRing A] [Algebra R k] [Algebra R L]
    (sR : Spec (CommRingCat.of R) ⟶ S)

    (ι : Spec (CommRingCat.of L) ⟶ G)
    (h1 : ι ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ sR)
    (hcl : IsClosedImmersion (pullback.lift (f := g) (g := sR) ι (Spec.map (CommRingCat.ofHom (algebraMap R L))) h1))

    (s : Spec (CommRingCat.of k) ⟶ S) (hs : s = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ sR)
    (a : L →+* A) (c : k →+* A)
    (hA : IsPullback (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom c))
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Spec.map (CommRingCat.ofHom (algebraMap R k))))
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s) :
    IsClosedImmersion (pullback.lift (f := g) (g := s) (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq) := by sorry
