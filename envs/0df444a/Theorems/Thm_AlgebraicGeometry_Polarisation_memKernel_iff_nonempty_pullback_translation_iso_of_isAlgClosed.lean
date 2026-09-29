-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
-- name    : AlgebraicGeometry.Polarisation.memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/3be72950-464c-5a45-9190-2a93033a62f2
-- title:
--   Membership in K(L) iff translation-invariance at k-points
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism carrying a relative group law $L$ (a functorial group structure `RelativeGroupLaw` on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ \cdots = t\}$ over $\operatorname{Spec} k$, with multiplication, unit and inverse, the group axioms, and naturality of multiplication under base change), and assume $L$ is commutative, i.e. its multiplication on $T$-points is commutative for every $t : T \to \operatorname{Spec} k$. Let $\mathcal L$ be a module on $A$ that is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit module, and let $y$ be an element of $L$-points over $\operatorname{Spec}$ of the structure map $k \to k$ (the commutativity hypothesis enters only through the formation of this additive group of points). Write $t$ for $\operatorname{Spec}$ of $\mathrm{id}_k$ and $x$ for the section of $f$ underlying $y$. Then $x$ lies in the kernel `Polarisation.MemKernel`, i.e. the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ on $A \times_{\operatorname{Spec} k} A$ is, locally over each point of the base after restriction along $p_2 : A \times_{\operatorname{Spec} k} A \to \operatorname{Spec} k$, isomorphic to the unit module, if and only if there exists an isomorphism between the pullback of $\mathcal L$ along the translation morphism $\mathrm{id}_A \cdot x : A \to A$ and $\mathcal L$ itself.
--
--   This is the standard description, over an algebraically closed field, of the group $K(\mathcal L)$ attached to an invertible module $\mathcal L$ on an abelian scheme: a $k$-point $y$ lies in $K(\mathcal L)$ exactly when $T_y^*\mathcal L \cong \mathcal L$. It converts the Mumford-bundle definition of the kernel, which is the form used in the construction of polarisations and the Rosati involution, into the translation-invariance criterion, and is used in the analysis of theta points and of the triviality of the kernel of a principal polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm MonoidalCategory

theorem AlgebraicGeometry.Polarisation.memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (y : L.AlgPoints hc k) :
    Polarisation.MemKernel f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap k k))) (RelativeGroupLaw.AlgPoints.toPoint y) ↔
      Nonempty ((Scheme.Modules.pullback (RiemannForm.translation f L (RelativeGroupLaw.AlgPoints.toPoint y))).obj 𝓛 ≅ 𝓛) := by sorry
