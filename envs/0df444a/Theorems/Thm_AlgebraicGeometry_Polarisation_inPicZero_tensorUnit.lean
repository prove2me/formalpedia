-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_tensorUnit
-- name    : AlgebraicGeometry.Polarisation.inPicZero_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/237f0f9e-1843-57bc-a61a-d23b94cfdb33
-- title:
--   The structure sheaf lies in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field (a type in the lowest universe), let $A$ be a scheme in the same universe, let $f : A \to \operatorname{Spec} k$ be a morphism to the spectrum of $k$, and let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ\!\!\!\text{-}\,f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$ and satisfying associativity, the unit laws and left inverses. The assertion is that the unit object $\mathbf{1}$ of the monoidal category of modules on $A$, namely the structure sheaf viewed as a module over the ring sheaf of $A$, satisfies the predicate `InPicZero` for $f$ and $L$: first, it is invertible in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of the module along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module on $U$; and second, for every $k$-point $x$ of $A$, that is, every morphism $\operatorname{Spec} k \to A$ splitting $f$, the pullback of the unit module along the translation morphism $A \to A$ determined by $x$ through $L$ is isomorphic to the unit module.
--
--   This records the trivial element of $\mathrm{Pic}^0(A)$ in the sense used here: the structure sheaf is invertible and is fixed by all translations. It serves as the base case and sanity check in the treatment of $\mathrm{Pic}^0$ and of the maps $\varphi_{\mathcal L}$ attached to line bundles, and is invoked in the statements about vanishing of $H^0$ and about fibre dimensions for bundles in $\mathrm{Pic}^0$, and in the construction of Rosati-compatible isomorphisms for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_inPicZero_tensorUnit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.inPicZero_tensorUnit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) :
    InPicZero f L (𝟙_ A.Modules) := by sorry
