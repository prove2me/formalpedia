-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
-- name    : AlgebraicGeometry.Polarisation.nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/058bd1a4-e7b4-5909-a6c1-a51209f74383
-- title:
--   Triviality of the Mumford bundle along the unit axes
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a `RelativeGroupLaw` for $f$: a functorial group law assigning to each $t : T \to \operatorname{Spec} S$ a multiplication, unit and inverse on the $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, subject to associativity, the two unit laws, left inversion, and naturality of the multiplication in $T$. Write $e = (L.\mathrm{one}\,(\mathbb{1}_{\operatorname{Spec} S})).1 : \operatorname{Spec} S \to A$ for the unit section. Let $N$ be a module on $A$ satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $A$ has an open neighbourhood $U$ with the restriction of $N$ to $U$ isomorphic to the unit module, and assume $e^{*}N$ is isomorphic to the unit module. The conclusion is a conjunction of two nonemptiness assertions: both the pullback of $\Lambda(N) = \mathrm{addMor}^{*}N \otimes (p_1^{*}N^{\vee} \otimes p_2^{*}N^{\vee})$ along $\mathrm{sliceAt}\,f\,(L.\mathrm{one}\,\mathbb{1})$, and the pullback along that slice of the pullback of $\Lambda(N)$ along the swap isomorphism of $A \times_S A$, are isomorphic to the tensor unit. Here $\mathrm{addMor}$ is the group law on $A \times_S A$ obtained by multiplying the two projections, $N^{\vee}$ is the internal hom into the unit, and the slice is the morphism $A \times_S \operatorname{Spec} S \to A \times_S A$ with components $p_1$ and $p_2$ followed by $e$.
--
--   This is the statement that Mumford's bundle $\Lambda(N) = \mu^{*}N \otimes p_1^{*}N^{\vee} \otimes p_2^{*}N^{\vee}$ attached to an invertible module $N$ with trivialised fibre at the unit section is trivial on each of the two axes $A \times e$ and $e \times A$, over an arbitrary affine base and with no commutativity assumption on the group law. It feeds the abelian-scheme package, being used for the corresponding statement about pullbacks of Mumford bundles in [`GoodReductionJacobian.AbelianSchemePropertyBundle`](def/JacJ1Iface.html#L22).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (he : Nonempty ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj N ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))))).obj (mumfordBundle f L N) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L N)) ≅ 𝟙_ _) := by sorry
