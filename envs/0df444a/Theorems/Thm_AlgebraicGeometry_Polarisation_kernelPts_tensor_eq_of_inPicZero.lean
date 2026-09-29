-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero
-- name    : AlgebraicGeometry.Polarisation.kernelPts_tensor_eq_of_inPicZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/66c136d4-5314-54e8-a57a-264508cc82d4
-- title:
--   A Pic⁰-twist does not change kernelPts
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over each $t : T \to \operatorname{Spec} k$, given by multiplication, unit and inversion operations satisfying associativity, the two unit laws and left inversion, and compatible with base change along morphisms $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\mathcal M$ be a sheaf of modules on $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $\mathcal M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules on $U$. Let $Q$ be a sheaf of modules on $A$ satisfying `InPicZero f L Q`: $Q$ is invertible and, for every point $x$ of $A$ over the identity of $\operatorname{Spec} k$, the pullback of $Q$ along the translation endomorphism $L.translate\ x$ of $A$ is isomorphic to $Q$. Then the two subsets $\mathrm{kernelPts}\ f\ L\ (\mathcal M \otimes Q)$ and $\mathrm{kernelPts}\ f\ L\ \mathcal M$ of the set of points of $A$ over the identity of $\operatorname{Spec} k$ coincide, where $\mathrm{kernelPts}\ f\ L\ \mathcal L$ consists of those $x$ for which the predicate `RelativeGroupLaw.IsInStabilizer` holds, i.e. the pullback of $\mathcal L$ along right multiplication by $x$ and the pullback of $\mathcal L$ along the first projection of the fibre product are locally isomorphic over the second projection.
--
--   This is the standard fact that the stabiliser scheme of $k$-points $K(\mathcal L)$ is unchanged by twisting $\mathcal L$ by a line bundle in $\mathrm{Pic}^0$, in the form $K(\mathcal M \otimes Q)(k) = K(\mathcal M)(k)$. It feeds into the analysis of $\mathrm{kernelPts}$ for tensor powers of a polarising bundle on a scheme with a relative group law, used in the argument bounding the relevant space of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelPts_tensor_eq_of_inPicZero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (Q : A.Modules) (hQ : InPicZero f L Q) :
    kernelPts f L (𝓜 ⊗ Q) = kernelPts f L 𝓜 := by sorry
