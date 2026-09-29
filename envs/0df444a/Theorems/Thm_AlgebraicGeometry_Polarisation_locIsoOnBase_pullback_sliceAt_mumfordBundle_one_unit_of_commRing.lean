-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/904dccdc-7280-5382-b0f0-d8eaad2d3987
-- title:
--   Unit slice of the Mumford bundle is locally trivial over the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec} S$ a morphism, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of $A$-points over arbitrary test morphisms $t\colon T\to\operatorname{Spec} S$, given by operations `mul`, `one`, `inv` satisfying associativity, the two unit laws, left inversion, and naturality of `mul` under base change of test schemes. Let $\mathcal L$ be a module over $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit sheaf of modules on $U$. Let $T$ be a commutative ring and $t\colon\operatorname{Spec} T\to\operatorname{Spec} S$ a morphism. Write $e=L.\mathrm{one}\,t$ for the unit $T$-point, $\mu =$ `addMor f L` for the morphism $A\times_S A\to A$ obtained by multiplying the two projections as points over $p_1\circ f$, and $\Lambda(\mathcal L)=\mu^*\mathcal L\otimes(p_1^*\mathcal L^\vee\otimes p_2^*\mathcal L^\vee)$ for the Mumford bundle on $A\times_S A$, the dual being the internal hom into the unit. Let $\sigma\colon A\times_S T\to A\times_S A$ be the slice at $e$, i.e. the morphism with components $\mathrm{pr}_A$ and $\mathrm{pr}_T\circ e$. The conclusion is that $\sigma^*\Lambda(\mathcal L)$ and the unit module on $A\times_S T$ are locally isomorphic over the base $\operatorname{Spec} T$ along $\mathrm{pr}_T=$ `pullback.snd f t`: for every point $s$ of $\operatorname{Spec} T$ there is an open $U\ni s$ such that the restrictions of $\sigma^*\Lambda(\mathcal L)$ and of the unit module to the open subscheme $\mathrm{pr}_T^{-1}(U)$ are isomorphic.
--
--   This is the statement that the unit section always lies in the kernel $K(\mathcal L)$ of the Mumford bundle, in the functor-of-points form used by the project's triviality predicates for $\Lambda(\mathcal L)$, over an arbitrary affine base rather than over an algebraically closed field. It serves as the normalisation input for the results identifying the kernel with a torsion condition, such as the two-torsion statement for the kernel after pulling back along the inversion morphism and the characterisation of membership in the kernel by a multiple condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (T : Type) [CommRing T] (t : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.one t))).obj (mumfordBundle f L 𝓛))
      (𝟙_ ((pullback f t).Modules)) := by sorry
