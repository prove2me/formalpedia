-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
-- name    : AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c9a561dc-f49d-58ca-8b8d-9eeed96256bb
-- title:
--   Twisting a symmetric square root by a symmetric 2-torsion bundle
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}R$ a morphism equipped with a relative group law $L$ (a functorial group structure on the sets of $f$-sections $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ over varying $T\to\operatorname{Spec}R$, natural in $T$), and write $[-1]$ for the inversion morphism `negMor f L` of $A$ obtained by applying $L$'s inverse operation to the identity point of $A$. For modules $M,M'$ on $A$, say $M\simeq_{\mathrm{loc}}M'$ when for every point $s$ of $\operatorname{Spec}R$ there is an open $U\ni s$ such that the pullbacks of $M$ and $M'$ to $f^{-1}(U)$ are isomorphic; and call $M$ symmetric when $[-1]^*M\simeq_{\mathrm{loc}}M$. Given modules $\mathcal L,\tau,N$ on $A$, each invertible in the sense that every point of $A$ has an open neighbourhood on which the restriction is isomorphic to the unit module, and given that $\tau$ is symmetric with $\mathcal L\simeq_{\mathrm{loc}}\tau\otimes[-1]^*\tau$, and that $N$ is symmetric with $N\otimes N\simeq_{\mathrm{loc}}\mathbf 1$, the conclusion is that $\tau\otimes N$ is again symmetric and that $\mathcal L\simeq_{\mathrm{loc}}(\tau\otimes N)\otimes[-1]^*(\tau\otimes N)$.
--
--   This is the statement that the symmetric $2$-torsion (admissible) invertible modules act on symmetric square roots of $\mathcal L$, in the form needed for a torsor structure on such square roots; everything is taken up to isomorphism Zariski-locally on the base $\operatorname{Spec}R$. It is used in the construction of the natural class functor attached to symmetric roots for abelian schemes with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit.lean

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

theorem AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 τ N : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hτ : Scheme.Modules.IsInvertible τ) (hN : Scheme.Modules.IsInvertible N)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hsN : IsSymmetric f L N) (h2N : LocIsoOnBase f (N ⊗ N) (𝟙_ A.Modules)) :
    IsSymmetric f L (τ ⊗ N) ∧ LocIsoOnBase f 𝓛 ((τ ⊗ N) ⊗ (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ N)) := by sorry
