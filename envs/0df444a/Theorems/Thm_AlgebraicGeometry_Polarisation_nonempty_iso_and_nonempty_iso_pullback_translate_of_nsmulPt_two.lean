-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_and_nonempty_iso_pullback_translate_of_nsmulPt_two
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_and_nonempty_iso_pullback_translate_of_nsmulPt_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/dd1395b5-1cdb-5089-a5ca-840e7c94dca6
-- title:
--   Symmetrising translate: Tₓ^*L symmetric when φ_L(2x) matches [-1]^*LotimesL^∨
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law for $f$: a rule assigning to every scheme $T$ with a morphism $t$ to $\operatorname{Spec} k$ a multiplication, unit and inverse on the set of $T$-sections $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws, left inverse, and compatibility of multiplication with base change along morphisms $\psi$ over $\operatorname{Spec} k$. Assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, i.e. every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$. Let $x, y$ be $k$-points of $A$ (sections of $f$ over the identity of $\operatorname{Spec} k$) with $y = (0 + x) + x$, the second iterate `nsmulPt L 2 x`. Write $[-1] =$ `negMor f L` for the inversion morphism obtained as the $L$-inverse of the identity section of $f$ over $A$, $T_z$ for the translation morphism `L.translate` by a $k$-point $z$, and $\mathcal L^\vee$ for the internal hom from $\mathcal L$ into the monoidal unit. Suppose there exists an isomorphism $([-1]^*\mathcal L \otimes \mathcal L^\vee) \otimes \mathcal L \cong T_y^*\mathcal L$ of modules on $A$. Then there exist isomorphisms $[-1]^*(T_x^*\mathcal L) \cong T_x^*\mathcal L$ and $T_x^*\mathcal L \otimes [-1]^*(T_x^*\mathcal L) \cong \mathcal L \otimes [-1]^*\mathcal L$; both conclusions assert mere nonemptiness of the sets of such isomorphisms.
--
--   This is the coherence step in the classical symmetrisation of a line bundle on an abelian variety: translating $\mathcal L$ by a point $x$ whose double $y$ corrects the defect $[-1]^*\mathcal L \otimes \mathcal L^\vee$ produces a symmetric bundle with the same symmetric square as $\mathcal L$. It is used in the construction of symmetric elements of the relevant Picard group with prescribed kernel data, and feeds the statements about symmetric line bundles attached to an abelian scheme over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_and_nonempty_iso_pullback_translate_of_nsmulPt_two.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.Polarisation.nonempty_iso_and_nonempty_iso_pullback_translate_of_nsmulPt_two
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hxy : nsmulPt L (𝟙 (Spec (CommRingCat.of k))) 2 x = y)
    (hν : Nonempty (((Scheme.Modules.pullback (negMor f L)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) ⊗ 𝓛 ≅
      (Scheme.Modules.pullback (L.translate y)).obj 𝓛)) :
    Nonempty ((Scheme.Modules.pullback (negMor f L)).obj ((Scheme.Modules.pullback (L.translate x)).obj 𝓛) ≅
        (Scheme.Modules.pullback (L.translate x)).obj 𝓛) ∧
    Nonempty ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗
          (Scheme.Modules.pullback (negMor f L)).obj ((Scheme.Modules.pullback (L.translate x)).obj 𝓛) ≅
        𝓛 ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛) := by sorry
