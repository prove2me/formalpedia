-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_twoAffineLineCover
-- name    : AlgebraicGeometry.exists_isProper_twoAffineLineCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/753f8368-2f6e-5e2a-9377-534347680c52
-- title:
--   Two-chart proper P¹ over an arbitrary commutative ring
-- statement:
--   For every commutative ring $S$ there exist a scheme $P$, a morphism $p \colon P \to \operatorname{Spec} S$ and two morphisms $i_0, i_1 \colon \operatorname{Spec} S[X] \to P$ with the following nine properties: $p$ is proper; $i_0$ and $i_1$ are open immersions; both composites $i_0$ followed by $p$ and $i_1$ followed by $p$ equal the morphism $\operatorname{Spec} S[X] \to \operatorname{Spec} S$ induced by the structure map $S \to S[X]$; the images of the underlying continuous maps of $i_0$ and $i_1$ cover the whole topological space of $P$; the two charts agree on the punctured line, namely the morphism $\operatorname{Spec} S[T,T^{-1}] \to \operatorname{Spec} S[X]$ dual to $X \mapsto T$ (`Polynomial.toLaurent`) followed by $i_0$ coincides with the morphism dual to $X \mapsto T^{-1}$ (`Polynomial.toLaurent` composed with the ring involution `LaurentPolynomial.invert`) followed by $i_1$; moreover that commuting square is cartesian, so $\operatorname{Spec} S[T,T^{-1}]$ is precisely the intersection of the two charts; and finally, if $S$ is a domain then $P$ is integral.
--
--   This packages the projective line over a commutative ring $S$ as an interface: a proper $S$-scheme covered by two copies of the affine line glued along $\operatorname{Spec} S[T,T^{-1}]$ by $T \mapsto T^{-1}$, with integrality over a domain. It is used in the study of homomorphisms out of $\operatorname{Spec} S[X]$ into abelian schemes, where the rigidity of maps from $\mathbb{P}^1$ forces a factorisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_twoAffineLineCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.exists_isProper_twoAffineLineCover (S : Type u) [CommRing S] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of S)) (i₀ i₁ : Spec (CommRingCat.of (Polynomial S)) ⟶ P),
      IsProper p ∧ IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      i₀ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      i₁ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ i₁ ∧
      IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))
        (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) i₀ i₁ ∧
      (IsDomain S → IsIntegral P) := by sorry
