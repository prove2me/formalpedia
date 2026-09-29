-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
-- name    : AlgebraicGeometry.Polarisation.H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/af79a6b8-d17d-5b2f-8681-145f8822e882
-- title:
--   Vanishing Čech cohomology of a non-trivial bundle in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $f$ over each $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative, and that `AbelianSchemePropertyBundle k f` holds, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} k$ is connected, and $f$ admits a relative group law. Let $M$ be a sheaf of modules on $A$ satisfying `InPicZero f L M`: $M$ is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with the pullback of $M$ along $U \hookrightarrow A$ isomorphic to the unit sheaf of modules of $U$, and for every point $x$ of $f$ over the identity of $\operatorname{Spec} k$ the pullback of $M$ along the translation $L.\mathrm{translate}\ x$ is isomorphic to $M$. Assume further that $M$ is not isomorphic to the unit object $\mathbb{1}$ of $A.\mathrm{Modules}$. Then, for every ordered affine cover $\mathcal{U}$ of $A$ (a finite family of affine opens indexed by a linearly ordered finite type, with supremum $\top$), the ordered Čech complex of the presheaf of $\mathcal{O}$-module sections `OModulePresheaf.ofModules f M` has $H^0(\mathcal{U}, M) = \bot$, the zero submodule of the $0$-cochains, and for every $i \in \mathbb{N}$ the group $\ker d^{i+1} / \operatorname{im} d^{i}$ in degree $i+1$ is a subsingleton, hence zero.
--
--   This is Mumford's acyclicity statement for a non-trivial invertible sheaf in $\operatorname{Pic}^0$ of an abelian variety (Abelian Varieties, §8 (vii)), here in the form of vanishing of the ordered Čech cohomology of $M$ with respect to an arbitrary finite ordered affine open cover. It is used in the computation of Čech ranks for Mumford bundles and their slices, and in the analysis of the kernel of the polarisation attached to an invertible sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.H0_eq_bot_and_subsingleton_HSucc_of_inPicZero_of_not_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : InPicZero f L M) (hM1 : ¬ Nonempty (M ≅ 𝟙_ (A.Modules))) (𝒰 : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules f M).H0 𝒰 = ⊥ ∧ ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules f M).HSucc 𝒰 i) := by sorry
