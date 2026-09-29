-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f1bcdb46-897b-5ef3-99c1-56e717e25019
-- title:
--   Slicing the Mumford bundle of [-1]^*L
-- statement:
--   Let $S$ be a commutative ring and $f : A \to \operatorname{Spec} S$ a morphism of schemes, equipped with a relative group law $L$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} S$, assumed commutative ($L.\mathrm{mul}\,t\,x\,y = L.\mathrm{mul}\,t\,y\,x$ for all $t,x,y$). Let $\mathcal L$ be a module sheaf on $A$ which is invertible, i.e. every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module sheaf. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and $x$ a section of $f$ over $t$. Write $N = \mathtt{negMor}\,f\,L$ for the inversion morphism $A \to A$, namely the underlying morphism of $L.\mathrm{inv}\,f\,\mathrm{id}_A$; write $\Lambda(\mathcal M) = \mu^*\mathcal M \otimes (p_1^*\mathcal M^\vee \otimes p_2^*\mathcal M^\vee)$ on $A \times_S A$ for the Mumford bundle, $\mu$ being the addition morphism of $L$; and write $(1,y) : A\times_S\operatorname{Spec} R \to A\times_S A$ for the slice $\mathtt{sliceAt}\,f\,y = (p_1, p_2 \circ y)$. The assertion is that the two module sheaves $(1,x)^*\Lambda(N^*\mathcal L)$ and $(N\times 1)^*\,(1,L.\mathrm{inv}\,t\,x)^*\Lambda(\mathcal L)$ on $A\times_S\operatorname{Spec} R$ are isomorphic, where $N\times 1$ is the morphism of $A\times_S\operatorname{Spec} R$ given by $(p_1 \circ N, p_2)$; the conclusion is the nonemptiness of the type of such isomorphisms, no particular isomorphism being named.
--
--   This is the compatibility of the Mumford (theorem-of-the-square) bundle $\Lambda$ with inversion, in the form needed to compare the slice of $\Lambda([-1]^*\mathcal L)$ at an $R$-point $x$ with the slice of $\Lambda(\mathcal L)$ at $x^{-1}$, over an arbitrary commutative base ring. It is used in the analysis of the kernel of the polarisation attached to $\mathcal L \otimes [-1]^*\mathcal L$ and its two-torsion, and in the membership criterion for kernels of tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛)) ≅
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst f t ≫ negMor f L) (pullback.snd f t)
          (by rw [Category.assoc, negMor_over]; exact pullback.condition))).obj ((Scheme.Modules.pullback (sliceAt f (L.inv t x))).obj (mumfordBundle f L 𝓛))) := by sorry
