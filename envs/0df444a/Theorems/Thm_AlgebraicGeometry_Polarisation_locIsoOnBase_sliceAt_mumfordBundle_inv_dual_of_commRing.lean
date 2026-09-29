-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/ce0904a4-78f9-56cd-ae12-8b80a8b7a07e
-- title:
--   Mumford bundle at x⁻¹ is locally the dual
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ on $f$ — that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of sections of $f$ over $t$, for all $t : T \to \operatorname{Spec} S$ — which is assumed commutative, and suppose $f$ satisfies `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre of the underlying map is connected, and $f$ admits a relative group law. Let $\mathcal{L}$ be a module on $A$ which is invertible (locally on $A$ isomorphic to the unit), and write $\Lambda$ for the Mumford bundle on $A \times_{\operatorname{Spec} S} A$, namely $m^{*}\mathcal{L} \otimes (\mathrm{pr}_1^{*}\mathcal{L}^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal{L}^{\vee})$, where $m$ is the addition morphism of $L$. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and $x$ a section of $f$ over $t$. Then the pullbacks of $\Lambda$ along the slices at $L.\mathrm{inv}\,t\,x$ and at $x$ — the slice at a section $y$ being the morphism $A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to A \times_{\operatorname{Spec} S} A$ with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by $y$ — satisfy the relation `LocIsoOnBase` with respect to the projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to \operatorname{Spec} R$: every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage the pullback of $\Lambda$ along the slice at $L.\mathrm{inv}\,t\,x$ becomes isomorphic to the dual of the pullback of $\Lambda$ along the slice at $x$.
--
--   This is the inversion case of the bilinearity of the Mumford bundle: over a general base $S$ the identification $\Lambda_{x^{-1}} \cong \Lambda_{x}^{\vee}$ is asserted only locally on the test base $\operatorname{Spec} R$. It feeds the analysis of the kernel of $x \mapsto \Lambda_x$ and its two-torsion behaviour under pullback along inversion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.inv t x))).obj (mumfordBundle f L 𝓛)) (Scheme.Modules.dual ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))) := by sorry
