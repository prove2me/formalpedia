-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/8da5bdb9-1dca-587d-b4f1-10de0228bd13
-- title:
--   Additivity of pair tangent coordinates along three lifts
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k =$ `ResidueField T'`, let $I \subseteq T'$ be an ideal contained in the maximal ideal with $I \cdot \mathfrak m = 0$, and let $V$ be a $k$-module, finite over $k$, carrying also right and $T'$-module structures compatible with the $k$-structure, together with a $T'$-linear injection $\iota : V \to T'$ whose image is exactly $I$ (as $T'$-submodule). Let $C$ be a flat $T'$-algebra, $q_Y : Y \to \operatorname{Spec} T'$ a scheme over $T'$, and $u, v, x : \operatorname{Spec} C \to Y$ three morphisms over $\operatorname{Spec} T'$ that become equal after pulling back along $\operatorname{Spec}(C/IC) \to \operatorname{Spec} C$ (the hypotheses state $u = v$ and $v = x$ modulo $I C$). Let $xk : Ak \to \operatorname{Spec} k$ carry a `RelativeGroupLaw` $Lk$, i.e. a functorial group structure on the sets of $k$-morphisms into $Ak$ over each $k$-scheme, natural in the base, and let $ak : Ak \to Y$ exhibit $Ak$ as the fibre of $q_Y$ over the residue map, the square with $xk$, $q_Y$ and $\operatorname{Spec}(\mathrm{residue})$ being a pullback. Let $Ue \subseteq Ak$ be an affine open with a $k$-point $e_1$ of $Ue$ whose composition with the open immersion is the unit section of $Lk$. Finally let $c_1, c_2, c_3$ assign to each section in $\Gamma(Ak, Ue)$ a $k$-linear map $\operatorname{Hom}_k(V,k) \to k \otimes_{T'} C$, and assume each satisfies `IsTangentCoordsOfPairAt` for the pairs $(u,v)$, $(v,x)$ and $(u,x)$ respectively: there are a morphism $w_0$ from the spectrum of the thickening $(k \otimes_{T'} C) \otimes_k \mathrm{TrivSqZeroExt}(k,V)$ to $Ak$ lying over the canonical base morphism, and a factorisation $w_1$ through $Ue$ of the $Lk$-translate of $w_0$ to the unit, such that $w_0$ followed by $ak$ is a tangent of the corresponding pair (a map of the pair ring into the thickening satisfying the Schlessinger condition, through which the two given morphisms factor) and the assignment is the tangent coordinate map attached to the induced chart ring homomorphism on $\Gamma(Ak, Ue)$. The conclusion is $c_3 = c_1 + c_2$.
--
--   This is the additivity of the difference cocycle measuring two lifts of a common reduction: the $T'$-lifts of a fixed morphism over $C/IC$ form a torsor under tangent fields along the special fibre, and the tangent coordinates of $(u,x)$ are the sum of those of $(u,v)$ and $(v,x)$, the group law of the special fibre contributing addition to first order. It is used in the chart-level computation of obstruction cocycles for abelian schemes with good reduction and in the multiplicativity and linearity statements derived from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u v x : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hx : x ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (hvx : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ x)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (c₁ c₂ c₃ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h₁ : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c₁)
    (h₂ : IsTangentCoordsOfPairAt I V ι C v x xk Lk ak Ue c₂)
    (h₃ : IsTangentCoordsOfPairAt I V ι C u x xk Lk ak Ue c₃) :
    c₃ = c₁ + c₂ := by sorry
