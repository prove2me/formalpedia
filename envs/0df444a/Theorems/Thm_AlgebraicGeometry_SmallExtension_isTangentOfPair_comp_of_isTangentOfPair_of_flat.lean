-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat
-- name    : AlgebraicGeometry.SmallExtension.isTangentOfPair_comp_of_isTangentOfPair_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/966919ce-985b-5d1a-92ae-76dda509bc3d
-- title:
--   Naturality of `IsTangentOfPair` along maps into flat algebras
-- statement:
--   Let $T'$ be a commutative local ring with residue field $k =$ `ResidueField T'`, let $I \subseteq T'$ be an ideal contained in the maximal ideal with $I \cdot \mathfrak{m} = 0$, and let $V$ be an abelian group carrying compatible left and right $k$-module structures with central scalars together with a $T'$-module structure forming a scalar tower over $k$. Let $\iota : V \to T'$ be an injective $T'$-linear map whose image is exactly $I$ viewed as a $T'$-submodule. Let $C$ and $C'$ be $T'$-algebras with $C'$ flat over $T'$, and $h : C \to C'$ a $T'$-algebra map. For a scheme $Y$, morphisms $u, v : \operatorname{Spec} C \to Y$ and $w : \operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C) \to Y$, where $\mathrm{thickening}\,T'\,V\,C = (k \otimes_{T'} C) \otimes_k \mathrm{TrivSqZeroExt}(k, V)$, assume `IsTangentOfPair I V ι C u v w`: there are a ring homomorphism $\vartheta$ from the pair ring $\{(a,b) \in C \times C : a \equiv b \bmod I C\}$ to $\mathrm{thickening}\,T'\,V\,C$ satisfying the two Schlessinger normalisations $\vartheta(a,a) = \bar a \otimes 1$ and $\vartheta(0, \iota(v) c) = \bar c \otimes \mathrm{inr}(v)$, and a morphism $\varphi : \operatorname{Spec}(\text{pair ring}) \to Y$ restricting along the two projections to $u$ and $v$ and with $w = \varphi \circ \operatorname{Spec}(\vartheta)$. Then `IsTangentOfPair I V ι C'` holds for $u \circ \operatorname{Spec}(h)$, $v \circ \operatorname{Spec}(h)$ and $w \circ \operatorname{Spec}(E_h)$, where $E_h = (\mathrm{id}_k \otimes h) \otimes \mathrm{id}$ is the induced $k$-algebra map $\mathrm{thickening}\,T'\,V\,C \to \mathrm{thickening}\,T'\,V\,C'$.
--
--   This is the naturality, in the affine chart, of the tangent datum attached to a pair of lifts over a small extension: the relative difference of $u$ and $v$, recorded by $w$ on the trivial square-zero thickening, is compatible with base change along any $T'$-algebra map into a flat algebra. It feeds the construction of tangent coordinates for pairs of lifts and their comparison under change of chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentOfPair_comp_of_isTangentOfPair_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] [Module.Flat T' C']
    (h : C →ₐ[T'] C')
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y) (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (huvw : IsTangentOfPair I V ι C u v w) :
    IsTangentOfPair I V ι C'
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u)
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v)
      (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
              (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
            thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom) ≫ w) := by sorry
