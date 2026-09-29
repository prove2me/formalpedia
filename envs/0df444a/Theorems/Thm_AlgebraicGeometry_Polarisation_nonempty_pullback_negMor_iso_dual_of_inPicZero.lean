-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_negMor_iso_dual_of_inPicZero
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_negMor_iso_dual_of_inPicZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1c8a4d97-7af2-5aed-a808-3b0c0b4c4bcd
-- title:
--   [-1]^*M≅ M^∨ for M in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$: a functorial group structure on the sets $\operatorname{Hom}_{/\operatorname{Spec} k}(T, A)$ of morphisms over a test morphism $t : T \to \operatorname{Spec} k$, given by operations `mul`, `one`, `inv` satisfying associativity, unit and left-inverse laws, with `mul` compatible with base change along morphisms of test schemes. Assume $L$ is commutative, i.e. `mul` is commutative on every test object, and that $f$ satisfies `AbelianSchemePropertyBundle`: $f$ is smooth, proper, has connected fibres over every point of $\operatorname{Spec} k$, and admits a relative group law. Let $M$ be a module on $A$ lying in $\operatorname{Pic}^0$ in the sense of `InPicZero`, that is: $M$ is invertible (every point of $A$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules on $U$), and for every $k$-point $x$ of $A$ (a morphism $\operatorname{Spec} k \to A$ over the identity of $\operatorname{Spec} k$) the pullback of $M$ along the translation $\mathrm{translate}\ L\ x$ is isomorphic to $M$. Then there exists an isomorphism between the pullback of $M$ along `negMor f L`, the morphism $A \to A$ underlying $L.\mathrm{inv}$ applied to the identity point of $A$ over $f$, and the dual $M^\vee$, defined as the internal hom from $M$ to the unit object in the monoidal category of modules on $A$.
--
--   This is the standard fact that on an abelian variety over an algebraically closed field the elements of $\operatorname{Pic}^0$ satisfy $[-1]^*M \cong M^\vee$ (Mumford, Abelian Varieties, §8). It feeds the further $\operatorname{Pic}^0$ manipulations `inPicZero_pullback_negMor_tensor_dual`, `nonempty_tensor_pullback_negMor_iso_of_inPicZero` and `subsingleton_sections_of_inPicZero_of_not_iso_unit`, used in the analysis of symmetric line bundles and polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_negMor_iso_dual_of_inPicZero.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_negMor_iso_dual_of_inPicZero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (M : A.Modules) (hM : InPicZero f L M) :
    Nonempty ((Scheme.Modules.pullback (negMor f L)).obj M ≅ Scheme.Modules.dual M) := by sorry
