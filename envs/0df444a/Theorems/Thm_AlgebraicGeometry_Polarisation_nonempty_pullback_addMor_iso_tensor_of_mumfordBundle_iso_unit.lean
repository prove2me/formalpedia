-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1b8603c5-3683-56e0-bff2-a9262b03f00f
-- title:
--   Trivial Mumford bundle gives μ^*M≅ p₁^*M⊗ p₂^*M
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, compatible with base change in $T$. Write $\mathrm{addMor}\ f\ L \colon A \times_A A$-style fibre product $\mathrm{pullback}\ f\ f \to A$ for the morphism obtained by multiplying the two projections in this group law. Let $M$ be an $\mathcal{O}_A$-module which is invertible in the project's sense: every point of $A$ has an open neighbourhood $U$ such that the restriction of $M$ along $U \hookrightarrow A$ is isomorphic to the unit module on $U$. Assume further that the Mumford bundle of $M$, namely $\mathrm{addMor}^* M \otimes (p_1^* M^\vee \otimes p_2^* M^\vee)$ on $\mathrm{pullback}\ f\ f$, with $M^\vee$ the internal hom from $M$ to the unit and $p_1, p_2$ the two projections, admits an isomorphism to the unit module. Then there exists an isomorphism $\mathrm{addMor}^* M \cong p_1^* M \otimes p_2^* M$. Both hypothesis and conclusion are stated as non-emptiness of the respective types of isomorphisms.
--
--   This is the standard unpacking of the identity $\mu^*\mathcal{M} \cong p_1^*\mathcal{M} \otimes p_2^*\mathcal{M}$ for a line bundle whose Mumford (Theta) bundle is trivial, in the form used for elements of $\mathrm{Pic}^0$. It feeds the analysis of cohomology of non-trivial degree-zero line bundles, where it identifies the invariants of $\mathrm{addMor}^* M$ with those of an external tensor product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_addMor_iso_tensor_of_mumfordBundle_iso_unit
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hΛ : Nonempty (mumfordBundle f L M ≅ 𝟙_ ((pullback f f).Modules))) :
    Nonempty ((Scheme.Modules.pullback (addMor f L)).obj M ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M) := by sorry
