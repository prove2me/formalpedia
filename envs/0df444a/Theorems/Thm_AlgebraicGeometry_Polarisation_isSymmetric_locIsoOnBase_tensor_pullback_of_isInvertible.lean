-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
-- name    : AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c675ed9c-fd0b-509d-ad73-c0b7ac419f4b
-- title:
--   Twisting by a line bundle from the base preserves symmetric square roots
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec} R$ a morphism, and $L$ a relative group law on $f$ (a functorial group structure on the sets of sections $T\to A$ over each $T\to\operatorname{Spec} R$); write $[-1]=$ `negMor f L` for the morphism $A\to A$ underlying the inverse of the identity section. Let $\mathcal L,\tau$ be sheaves of modules on $A$ and $D$ a sheaf of modules on $\operatorname{Spec} R$ which is invertible, i.e. every point of $\operatorname{Spec} R$ has an open neighbourhood on which the restriction of $D$ is isomorphic to the unit module. Here two modules $M,M'$ on $A$ are called isomorphic locally on the base when for every point $s$ of $\operatorname{Spec} R$ there is an open $U\ni s$ such that the pullbacks of $M$ and $M'$ along the inclusion $f^{-1}(U)\hookrightarrow A$ are isomorphic; $\tau$ being symmetric means $[-1]^*\tau$ and $\tau$ are isomorphic locally on the base. Assume $\tau$ is symmetric and that $\mathcal L$ and $\tau\otimes[-1]^*\tau$ are isomorphic locally on the base. Then the twist $\tau\otimes f^*D$ is again symmetric, and $\mathcal L$ is isomorphic, locally on the base, to $(\tau\otimes f^*D)\otimes[-1]^*(\tau\otimes f^*D)$.
--
--   This is the statement that the property of being a symmetric square root of $\mathcal L$, in the sense of isomorphism locally on the base, is insensitive to twisting by the pullback of an invertible module from the affine base. It is used in the construction of rigidified symmetric square roots, where a given symmetric square root is altered by such a twist, in [`AlgebraicGeometry.SymmRoot.exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange`](thm.html#AlgebraicGeometry.SymmRoot.exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange) and [`AlgebraicGeometry.SymmRoot.exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase`](thm.html#AlgebraicGeometry.SymmRoot.exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 τ : A.Modules) (D : (Spec (CommRingCat.of R)).Modules) (hD : Scheme.Modules.IsInvertible D)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ)) :
    IsSymmetric f L (τ ⊗ (Scheme.Modules.pullback f).obj D) ∧
      LocIsoOnBase f 𝓛 ((τ ⊗ (Scheme.Modules.pullback f).obj D) ⊗
        (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ (Scheme.Modules.pullback f).obj D)) := by sorry
