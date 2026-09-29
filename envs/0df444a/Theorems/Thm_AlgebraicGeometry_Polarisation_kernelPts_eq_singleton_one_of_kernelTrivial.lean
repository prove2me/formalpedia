-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_eq_singleton_one_of_kernelTrivial
-- name    : AlgebraicGeometry.Polarisation.kernelPts_eq_singleton_one_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1786dbd2-7546-5bea-b876-1e928bb72daa
-- title:
--   Trivial kernel forces the stabiliser points to be {e}
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a relative group law for $f$, i.e. functorial multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $f$ over arbitrary $S$-schemes $t : T \to \operatorname{Spec} S$, satisfying associativity, the unit laws, left inversion and compatibility with base change along morphisms $\psi$ with $t \circ \psi = t'$. Let $\mathcal{L}_0$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $\mathcal{L}_0$ is isomorphic to the unit module of $U$. Assume `KernelTrivial f L 𝓛₀`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $f$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $\Lambda(\mathcal{L}_0) = m^{*}\mathcal{L}_0 \otimes (p_1^{*}\mathcal{L}_0^{\vee} \otimes p_2^{*}\mathcal{L}_0^{\vee})$ on $A \times_{\operatorname{Spec} S} A$ becomes isomorphic to the unit module locally on $\operatorname{Spec} R$ (i.e. after pullback to the preimage under the second projection of some open neighbourhood of each point of $\operatorname{Spec} R$), then $x = L.\mathrm{one}\,t$. The conclusion is that `kernelPts f L 𝓛₀`, the set of sections $x$ of $f$ over $\mathrm{id}_{\operatorname{Spec} S}$ for which the pullback of $\mathcal{L}_0$ along right translation by $x$ and the pullback of $\mathcal{L}_0$ along the first projection of $A \times_{\operatorname{Spec} S} \operatorname{Spec} S$ are isomorphic locally over the base along the second projection, is exactly the singleton consisting of the unit section $L.\mathrm{one}\,(\mathrm{id}_{\operatorname{Spec} S})$.
--
--   This is the statement that an invertible module whose stabiliser (the scheme-theoretic kernel $K(\mathcal{L}_0)$ of the map to the Picard functor) is trivial has only the identity among its $S$-rational stabiliser points, reconciling the two bookkeeping forms of the stabiliser condition: translation invariance of $\mathcal{L}_0$ on the one hand, and triviality of the slice of the Mumford bundle $\Lambda(\mathcal{L}_0)$ on the other. It is used to supply finiteness-of-`kernelPts` hypotheses, notably in the construction of closed immersions by sections of tensor powers of a canonical polarisation on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelPts_eq_singleton_one_of_kernelTrivial.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.kernelPts_eq_singleton_one_of_kernelTrivial
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    kernelPts f L 𝓛₀ = {L.one (𝟙 (Spec (CommRingCat.of S)))} := by sorry
