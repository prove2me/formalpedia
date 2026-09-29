-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/26bbd190-2b9e-5041-aa49-75dc431d6316
-- title:
--   Inversion pull-back of a Mumford slice is its dual, locally
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes, and $L$ a relative group law on $f$: a rule assigning to every $t : T \to \operatorname{Spec} S$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} S$. Assume $L$ is commutative and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module over $A$ which is invertible, in the sense that each point of $A$ has an open neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit module. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and $x$ an $R$-point of $A$ over $t$, i.e. $x : \operatorname{Spec} R \to A$ with $x$ followed by $f$ equal to $t$. Write $\Lambda(\mathcal L) = m^{*}\mathcal L \otimes (p_1^{*}\mathcal L^{\vee} \otimes p_2^{*}\mathcal L^{\vee})$ for the Mumford bundle on $A \times_S A$, where $m$ is the addition morphism attached to $L$ and $\mathcal L^{\vee}$ is the internal hom into the unit; let $\Lambda_x$ be its pull-back along $(p_1, x \circ p_2) : A \times_S \operatorname{Spec} R \to A \times_S A$, and let $[-1] \times 1 : A \times_S \operatorname{Spec} R \to A \times_S \operatorname{Spec} R$ be $(\,\nu \circ p_1,\, p_2)$, with $\nu : A \to A$ the inversion morphism obtained by applying the inverse of $L$ to the identity point of $A$ over $f$. The conclusion is that $([-1] \times 1)^{*}\Lambda_x$ and $\Lambda_x^{\vee}$ are locally isomorphic over the base $p_2 : A \times_S \operatorname{Spec} R \to \operatorname{Spec} R$: every point $s$ of $\operatorname{Spec} R$ has an open neighbourhood $U$ such that the pull-backs of the two modules along the inclusion of $p_2^{-1}(U)$ are isomorphic.
--
--   This is the anti-invariance $([-1] \times 1)^{*}\Lambda(\mathcal L)_x \cong \Lambda(\mathcal L)_x^{\vee}$ of the Mumford bundle in the first variable, a consequence of the theorem of the cube; over a general base the isomorphism is asserted only locally on the base, the discrepancy being a line bundle pulled back from $\operatorname{Spec} R$. It is used in the study of the kernel $K(\mathcal L)$, namely to show that the kernel of $\Lambda_x \otimes ([-1]\times 1)^{*}\Lambda_x$ consists of two-torsion points and to identify membership in kernels under tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f t ≫ negMor f L) (pullback.snd f t)
          (by rw [Category.assoc, negMor_over]; exact pullback.condition))).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)))
      (Scheme.Modules.dual ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))) := by sorry
