-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_of_forall_comp_mem_kernelPts
-- name    : AlgebraicGeometry.Polarisation.inPicZero_pullback_of_forall_comp_mem_kernelPts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/62fd7f9d-9200-55f8-a3d7-f0d9df7bcf0d
-- title:
--   Pullback along a homomorphism into K(L) lies in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, and work with schemes in the bottom universe. Let $f : A \to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L$, that is, functorially in $T \to \operatorname{Spec} k$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and compatibility with base change along morphisms $T' \to T$ over $k$) on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$. Let $fY : Y \to \operatorname{Spec} k$ carry a relative group law $LY$, and let $j : Y \to A$ be a closed immersion with $j$ followed by $f$ equal to $fY$, which is a homomorphism in the sense that for all $T \to \operatorname{Spec} k$ and all $T$-points $P, Q$ of $Y$, the point $LY.\mathrm{mul}\,P\,Q$ followed by $j$ equals $L.\mathrm{mul}$ of the images of $P$ and $Q$ under $j$. Let $\mathcal L$ be a module on $A$ which is invertible (locally on $A$ its pullback to a member of an open cover is isomorphic to the unit module), and assume that for every $k$-point $y$ of $Y$ the $k$-point $y$ followed by $j$ lies in $\mathrm{kernelPts}\ f\ L\ \mathcal L$, i.e. satisfies $L$'s stabiliser condition for $\mathcal L$ at the identity base. Then $j^{*}\mathcal L$ satisfies `InPicZero` for $fY$ and $LY$: it is invertible, and for every $k$-point $y$ of $Y$ the pullback of $j^{*}\mathcal L$ along the translation $LY.\mathrm{translate}\,y$ of $Y$ is isomorphic to $j^{*}\mathcal L$.
--
--   This is the standard fact that the restriction of a line bundle to a subgroup scheme contained in the stabiliser $K(\mathcal L)$ is translation-invariant, hence lies in $\operatorname{Pic}^0$. It feeds the computation of Čech invariants for such pullbacks, being used by `cechFinrank_eq_zero_of_forall_comp_mem_kernelPts_of_not_nonempty_pullback_iso_unit`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_of_forall_comp_mem_kernelPts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.inPicZero_pullback_of_forall_comp_mem_kernelPts
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (LY : RelativeGroupLaw k fY)
    (hj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fY),
      (LY.mul t P Q).1 ≫ j =
        (L.mul t ⟨P.1 ≫ j, by rw [Category.assoc, hjf, P.2]⟩ ⟨Q.1 ≫ j, by rw [Category.assoc, hjf, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hstab : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      (⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) ∈ kernelPts f L 𝓛) :
    InPicZero fY LY ((Scheme.Modules.pullback j).obj 𝓛) := by sorry
