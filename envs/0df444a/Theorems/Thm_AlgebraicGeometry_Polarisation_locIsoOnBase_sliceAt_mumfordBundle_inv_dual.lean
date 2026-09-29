-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_inv_dual
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_inv_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1f28fea6-2d73-5832-8d38-9462a4be3709
-- title:
--   Slice of the Mumford bundle at x⁻¹ is the dual slice
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, equipped with a relative group law $L$ on $f$ — a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ t^{-1}\text{-compatible, i.e. } \varphi \text{ followed by } f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverse cancellation and naturality of multiplication in $T$ — which is assumed commutative, and with the property bundle `AbelianSchemePropertyBundle` for $f$ (smoothness, properness, connected fibres, existence of a relative group law). Let $\mathcal{L}$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood on which the restriction of $\mathcal{L}$ is isomorphic to the unit. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} k$, and $x$ an $R$-point of $A$ over $t$. Write $\Lambda = \mathrm{mumfordBundle}\,f\,L\,\mathcal{L} = m^{*}\mathcal{L} \otimes (p_1^{*}\mathcal{L}^{\vee} \otimes p_2^{*}\mathcal{L}^{\vee})$ on $A \times_{\operatorname{Spec} k} A$, where $m$ is the morphism given by $L$, and for an $R$-point $y$ let $\mathrm{sliceAt}\,f\,y : A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to A \times_{\operatorname{Spec} k} A$ be $(p_1, p_2 \text{ followed by } y)$. Then the pullback of $\Lambda$ along $\mathrm{sliceAt}\,f\,(L.\mathrm{inv}\,t\,x)$ and the dual of the pullback of $\Lambda$ along $\mathrm{sliceAt}\,f\,x$ are locally isomorphic over the base: for every point $s$ of $\operatorname{Spec} R$ there is an open $U \ni s$ such that the two modules become isomorphic after restriction to the preimage of $U$ under the projection $A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to \operatorname{Spec} R$.
--
--   This is the scheme-theoretic form of the identity $\varphi_{\mathcal{L}}(-x) = -\varphi_{\mathcal{L}}(x)$ for the map from points of an abelian variety to the relative Picard group attached to a line bundle $\mathcal{L}$, here recorded only up to isomorphism locally on the base $\operatorname{Spec} R$. It is used in the analysis of the kernel of $\varphi_{\mathcal{L}}$ and its two-torsion behaviour under the inverse morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_inv_dual.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_inv_dual
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.inv t x))).obj (mumfordBundle f L 𝓛)) (Scheme.Modules.dual ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))) := by sorry
