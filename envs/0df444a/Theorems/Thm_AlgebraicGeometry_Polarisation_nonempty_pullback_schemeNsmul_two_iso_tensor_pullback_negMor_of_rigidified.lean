-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/8f4b057a-c21c-5c65-9056-4a1d3dbdea32
-- title:
--   Theorem of the square for [2] over an affine base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law on $f$: a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality of multiplication under base change of the test scheme) on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for every $t : T \to \operatorname{Spec} S$. Assume $L$ is commutative, i.e. its multiplication on every such set of $T$-points is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ carries some relative group law. Let $R$ be a commutative ring and $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism, and write $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ with structure morphism $\mathrm{pr}_2$ and the base-changed group law $L_R$. Let $N$ be a rigidified line bundle for $f$ along the unit section of $L$ over $\iota$: a module $N.L$ on $A_R$ which is locally trivial of rank one (each point has a neighbourhood $U$ with the restriction of $N.L$ to $U$ isomorphic to the unit module), together with an isomorphism of its pullback along the rigidifying section with the unit module on $\operatorname{Spec} R$. The conclusion is that there exists an isomorphism of modules on $A_R$
--   $$[2]^{*} N.L \;\cong\; (N.L \otimes N.L \otimes N.L) \otimes [-1]^{*} N.L,$$
--   where $[2]$ is the doubling endomorphism `schemeNsmul` of $L_R$ at $n = 2$ and $[-1]$ is the inversion morphism `negMor` of $L_R$.
--
--   This is the relative form, over an arbitrary affine base and without reducedness hypotheses, of the case $n = 2$ of the standard consequence of the theorem of the cube, $[n]^{*}N \cong N^{\otimes n(n+1)/2} \otimes ([-1]^{*}N)^{\otimes n(n-1)/2}$. It is used in the construction of polarisations, in the two statements relating local triviality of $[-1]^{*}N$ and of $N \otimes N$ to triviality of $[2]^{*}N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TorsionCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅
      (N.L ⊗ N.L ⊗ N.L) ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) := by sorry
