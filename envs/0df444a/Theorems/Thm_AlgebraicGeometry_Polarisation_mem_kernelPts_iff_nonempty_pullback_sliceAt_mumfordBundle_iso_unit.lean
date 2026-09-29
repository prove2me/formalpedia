-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
-- name    : AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/77c03c1d-73c7-5bf0-bdda-95741ee1016c
-- title:
--   k-points of K(L) via triviality of the sliced Mumford bundle
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme (in universe $0$) and $f : A \to \operatorname{Spec} k$ a morphism equipped with a relative group law $L$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$, natural in $T$. Let $\mathcal L$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit sheaf of modules on $U$, and let $x$ be a morphism $\operatorname{Spec} k \to A$ with $x$ followed by $f$ equal to $\mathrm{id}_{\operatorname{Spec} k}$. The assertion is an equivalence. On the one side, $x$ belongs to `kernelPts f L 𝓛`, that is, $L.\mathrm{IsInStabilizer}$ holds for $\mathcal L$ at the test object $\mathrm{id}_{\operatorname{Spec} k}$ and the point $x$: the pullback of $\mathcal L$ along the right translation by $x$ and the pullback of $\mathcal L$ along the first projection of $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ are `LocallyIsoOver` the second projection. On the other side, there exists an isomorphism of modules on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ (the pullback of $f$ along $\mathrm{id}$) between the pullback along $\mathrm{sliceAt}\,f\,x = (p_1, p_2 \circ x)$ of the Mumford bundle $\mu^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ on $A \times_{\operatorname{Spec} k} A$ and the monoidal unit, where $\mu$ is the addition morphism attached to $L$ and $\mathcal L^\vee$ is the internal hom from $\mathcal L$ to the unit.
--
--   This is the $k$-point case of the standard characterisation of the stabiliser $K(\mathcal L)$ of an invertible sheaf on an abelian variety, in the form: $x \in K(\mathcal L)(k)$ precisely when the slice at $x$ of the Mumford bundle $\Lambda(\mathcal L) = \mu^*\mathcal L \otimes p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee$ is trivial. It is used in the dual-free treatment of $\mathrm{Pic}^0$ and of the morphism $\varphi_{\mathcal L}$ for polarised abelian schemes, and is cited in the study of triviality of $K(\mathcal L)$ and of translations of the Mumford bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅ 𝟙_ ((pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules)) := by sorry
