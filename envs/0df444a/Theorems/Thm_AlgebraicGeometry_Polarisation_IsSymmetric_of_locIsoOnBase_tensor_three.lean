-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_IsSymmetric_of_locIsoOnBase_tensor_three
-- name    : AlgebraicGeometry.Polarisation.IsSymmetric.of_locIsoOnBase_tensor_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4feea7ee-8400-582d-b756-a63d23259e27
-- title:
--   Symmetry descends from a local cube root
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec}(S)$ be a morphism, and let $L$ be a relative group law for $f$ over $S$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec}(S)$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverse, and naturality in $T$. Write $[-1] :=$ `negMor f L` for the endomorphism of $A$ underlying the $L$-inverse of the identity point, and say that two modules $M, M'$ on a scheme over $\operatorname{Spec}(S)$ are locally isomorphic on the base when every point $s$ of $\operatorname{Spec}(S)$ lies in an open $U$ such that the pullbacks of $M$ and $M'$ along the inclusion of $f^{-1}(U)$ are isomorphic; call a module $\mathcal N$ on $A$ symmetric when $[-1]^*\mathcal N$ and $\mathcal N$ are locally isomorphic on the base. Given modules $\mathcal L$ and $\mathcal E$ on $A$ with $\mathcal E$ symmetric, and with $\mathcal L$ locally isomorphic on the base to $\mathcal E \otimes (\mathcal E \otimes \mathcal E)$, the conclusion is that $\mathcal L$ is symmetric.
--
--   This is the standard observation that symmetry of a line bundle on an abelian scheme, in the weak sense of an isomorphism with its pullback along inversion existing locally on the base, is inherited by anything that is locally a third tensor power of a symmetric bundle. It is used in the construction of rooted symmetric data of type $(6,6)$ attached to a quaternionic multiplication structure on a polarised abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_IsSymmetric_of_locIsoOnBase_tensor_three.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.IsSymmetric.of_locIsoOnBase_tensor_three
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : GoodReductionJacobian.RelativeGroupLaw S f)
    (𝓛 polE : A.Modules) (hsym : IsSymmetric f L polE) (hloc : LocIsoOnBase f 𝓛 (polE ⊗ polE ⊗ polE)) :
    IsSymmetric f L 𝓛 := by sorry
