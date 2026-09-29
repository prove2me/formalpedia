-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
-- name    : AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c0f04706-e8b3-51e6-b99b-c71fe8352da2
-- title:
--   Two symmetric square roots differ by an admissible bundle
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec} R$ a morphism, equipped with a `RelativeGroupLaw` $L$ for $f$, i.e. functorial group structures on the sets of sections $T\to A$ over each $T\to\operatorname{Spec} R$, natural in $T$; write $[-1]=$ `negMor f L` for the underlying endomorphism of $A$ obtained by inverting the identity section. Assume further the bundle `AbelianSchemePropertyBundle R f`: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L,\tau,\tau'$ be $\mathcal O_A$-modules, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction is isomorphic to the unit module. Assume $\tau$ and $\tau'$ are symmetric and are square roots of $\mathcal L$, both conditions in the sense `LocIsoOnBase`, i.e. every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage $f^{-1}(U)$ the two modules in question become isomorphic: symmetry says $[-1]^*\tau\cong\tau$ and $[-1]^*\tau'\cong\tau'$ in this local sense, and the square root conditions say $\mathcal L\cong\tau\otimes[-1]^*\tau$ and $\mathcal L\cong\tau'\otimes[-1]^*\tau'$ in this local sense. Then, setting $N:=\tau'\otimes\tau^{\vee}$ with $\tau^{\vee}$ the internal hom from $\tau$ to the unit: $N$ is symmetric, $N\otimes N$ is locally on the base isomorphic to the unit module, and there is a global isomorphism $\tau\otimes N\cong\tau'$.
--
--   This is the statement that two symmetric square roots of a line bundle on an abelian scheme differ by an "admissible" bundle, symmetric and $2$-torsion locally over the base, which carries one root to the other; classically such classes correspond to points of the Cartier dual of $A[2]$. It feeds the construction of symmetric roots compatible with the class functor used in the Jacobian good-reduction package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase.lean

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

theorem AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 τ τ' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hτ : Scheme.Modules.IsInvertible τ) (hτ' : Scheme.Modules.IsInvertible τ')
    (hsτ : IsSymmetric f L τ) (hsτ' : IsSymmetric f L τ')
    (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hrτ' : LocIsoOnBase f 𝓛 (τ' ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ')) :
    IsSymmetric f L (τ' ⊗ Scheme.Modules.dual τ) ∧
      LocIsoOnBase f ((τ' ⊗ Scheme.Modules.dual τ) ⊗ (τ' ⊗ Scheme.Modules.dual τ)) (𝟙_ A.Modules) ∧
      Nonempty (τ ⊗ (τ' ⊗ Scheme.Modules.dual τ) ≅ τ') := by sorry
