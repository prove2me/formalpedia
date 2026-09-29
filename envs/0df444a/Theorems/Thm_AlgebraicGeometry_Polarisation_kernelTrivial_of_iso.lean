-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2bf91512-7918-5b86-a3d0-d0e9e511a105
-- title:
--   Kernel triviality depends only on the isomorphism class
-- statement:
--   Fix a commutative ring $S$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} S$, together with a relative group law $L$ on $f$, i.e. operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the $T$-points $\{\varphi : T \to A \mid \varphi \circ' f = t\}$ of $f$ over each $t : T \to \operatorname{Spec} S$, satisfying the group axioms and compatibility of multiplication with base change along morphisms $T' \to T$ over $\operatorname{Spec} S$. Let $M$ and $M'$ be objects of `A.Modules` and $e : M \cong M'$ an isomorphism between them. The assertion is that `KernelTrivial f L` transfers from $M$ to $M'$: if for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $A$ over $t$ (a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is $t$), the pullback along $\operatorname{sliceAt} f x = \langle \mathrm{pr}_1, x \circ \mathrm{pr}_2\rangle : A\times_{\operatorname{Spec} S}\operatorname{Spec} R \to A \times_{\operatorname{Spec} S} A$ of the Mumford bundle $\Lambda(M) = \mathrm{add}^{*}M \otimes (\mathrm{pr}_1^{*}M^{\vee} \otimes \mathrm{pr}_2^{*}M^{\vee})$ is isomorphic to the tensor unit after restriction to $\mathrm{pr}_2^{-1}(U)$ for some open $U$ around each point of $\operatorname{Spec} R$, forces $x$ to be the identity section $L.\mathrm{one}\,t$, then the same implication holds with $M$ replaced by $M'$.
--
--   This says that the condition '$K(\mathcal L)$ is trivial', defining when the Mumford bundle attached to a module on a relative group scheme has trivial kernel, is invariant under isomorphism of the module. It is used to move such a hypothesis between isomorphic modules (for instance from a bundle on a generic fibre to a pullback of a given bundle), and is cited in the construction of symmetric principal polarisation data on abelian schemes and on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelTrivial_of_iso
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (M M' : A.Modules) (e : M ≅ M') (h : KernelTrivial f L M) :
    KernelTrivial f L M' := by sorry
