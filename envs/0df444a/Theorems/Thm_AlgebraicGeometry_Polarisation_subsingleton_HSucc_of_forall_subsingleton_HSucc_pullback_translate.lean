-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
-- name    : AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/dab5ac23-1d92-5663-8c5f-bae6f679b7e5
-- title:
--   Translation invariance of vanishing of higher Čech groups
-- statement:
--   Let $k$ be an algebraically closed field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes (in universe $0$). Let $L$ be a relative group law for $f$ in the sense of the project: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, the two unit laws and left inverse, and with multiplication compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$; assume $L$ is commutative. Assume further the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal M$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $(\,\cdot\,)|_U$, the pullback of $\mathcal M$ along $U \hookrightarrow A$, isomorphic to the unit sheaf of modules on $U$, and let $x$ be a point of $A$ over $\operatorname{Spec} k$, i.e. a section $x$ of $f$ over the identity of $\operatorname{Spec} k$, with associated translation endomorphism $L.\mathrm{translate}\,x : A \to A$ given by the product of the identity point with the constant point $x$. Suppose that for every ordered affine cover $\mathcal U$ of $A$ (a finite, linearly ordered family of affine opens whose supremum is $\top$) and every $i \in \mathbb N$, the group $\check H^{i+1}(\mathcal U, \cdot) = \ker d^{i+1} / \operatorname{im} d^{i}$ of the $\mathcal O$-module presheaf of sections of the pullback of $\mathcal M$ along $L.\mathrm{translate}\,x$ is a subsingleton. Then, for every ordered affine cover $\mathcal U$ of $A$ and every $i$, the corresponding group $\check H^{i+1}(\mathcal U, \mathcal M)$ attached to $\mathcal M$ itself is a subsingleton.
--
--   This is the translation-invariance step in the cohomological study of line bundles on an abelian scheme over a field: vanishing of the higher Čech groups of a translate $T_x^*\mathcal M$ forces the same vanishing for $\mathcal M$, on every finite ordered affine cover. It feeds into the criterion [`AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos`](thm.html#AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos), where higher cohomology of an ample-type invertible module is shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate.lean

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

theorem AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (h : ∀ (𝒰 : A.OrderedAffineCover) (i : ℕ),
      Subsingleton ((OModulePresheaf.ofModules f ((Scheme.Modules.pullback (L.translate x)).obj 𝓜)).HSucc 𝒰 i))
    (𝒰 : A.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules f 𝓜).HSucc 𝒰 i) := by sorry
