-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
-- name    : AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ce3d9430-16d7-5c6d-8b8d-a77a02e41e82
-- title:
--   Tangent maps into an affine chart versus point derivations
-- statement:
--   Let $T'$ be a local ring with residue field $k = \mathrm{ResidueField}\,T'$, let $V$ be a $k$-vector space (with left, right and central $k$-actions, finite over $k$, and a $T'$-action compatible with $k$ via the scalar tower), and let $C$ be a commutative $T'$-algebra; write $C_k = k \otimes_{T'} C$ and $E = \mathrm{thickening}\,T'\,V\,C = C_k \otimes_k \mathrm{TrivSqZeroExt}(k,V)$. Let $Ak$ be a scheme with a morphism $xk : Ak \to \operatorname{Spec} k$, let $pt : \operatorname{Spec} k \to Ak$ satisfy $xk \circ pt = \mathrm{id}$, let $Ue \subseteq Ak$ be an affine open and $e_1 : \operatorname{Spec} k \to Ue$ a morphism with $Ue.\iota \circ e_1 = pt$. Give $\Gamma(Ak, Ue)$ the $k$-algebra structure induced by $xk$, and let $\mathrm{ev}$ be the ring homomorphism $\Gamma(Ak,Ue) \to k$ obtained from $e_1$ on sections. Call $w_1 : \operatorname{Spec} E \to Ue$ admissible when the composite $\operatorname{Spec} E \to Ue \to Ak \to \operatorname{Spec} k$ equals $\mathrm{thickeningSnd}$ followed by $\mathrm{SquareZero.toBase}\,k\,V$, and the restriction of $Ue.\iota \circ w_1$ along $\mathrm{SquareZero.zeroSection}$ for the pullback square $\mathrm{thickening\_isPullback}$ equals $\mathrm{reductionBase}\,T'\,C$ followed by $pt$. For such $w_1$ let $\mathrm{tangentCoords}$ applied to the induced ring map $\Gamma(Ak,Ue) \to E$ be the map sending $a$ to the image of the $V$-component of $w_1^{\sharp}(a)$ in $C_k \otimes_k V$ under the canonical map to $\mathrm{Hom}_k(V^{\vee}, C_k)$. The theorem asserts three things: first, for every admissible $w_1$ this map agrees pointwise with an element of the submodule $\mathrm{Algebra.PointDerivations}\,k\,\Gamma(Ak,Ue)\,\mathrm{ev}$ with values in $\mathrm{Hom}_k(V^{\vee}, C_k)$, that is, of the $k$-linear maps $D$ with $D(ab) = \mathrm{ev}(a)D(b) + \mathrm{ev}(b)D(a)$; second, two admissible $w_1, w_1'$ with the same tangent coordinates are equal; third, every such point derivation is, pointwise, the tangent coordinates of some admissible $w_1$.
--
--   This is the value-level identification of the relative tangent vectors at the rational point $pt$, parametrised by $\operatorname{Spec}(k \otimes_{T'} C)$ and read inside an affine chart $Ue$, with the point derivations of the chart's coordinate ring at that point, with values in $\mathrm{Hom}_k(V^{\vee}, k \otimes_{T'} C)$. It supplies the existence, uniqueness and surjectivity statements used by the lemmas characterising the tangent coordinates of a pair at a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak) (hpt : pt ≫ xk = 𝟙 _)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt) :
    letI := algebraOfHom xk Ue
    (∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        ∃ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) ∧
    (∀ w₁ w₁' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        (w₁' ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁' ≫ Ue.ι = reductionBase T' C ≫ pt →
        tangentCoords T' V C (chartRingHom V C Ue w₁) = tangentCoords T' V C (chartRingHom V C Ue w₁') → w₁ = w₁') ∧
    (∀ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
        ∃ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
          (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) ∧
          SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
              ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt ∧
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) := by sorry
