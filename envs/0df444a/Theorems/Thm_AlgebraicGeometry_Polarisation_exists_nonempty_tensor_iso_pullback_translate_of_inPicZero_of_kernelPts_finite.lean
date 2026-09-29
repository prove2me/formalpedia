-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
-- name    : AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/490702b6-0455-5d16-910d-73a9d61989ea
-- title:
--   Surjectivity of φ_L onto Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a functorially assigned group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, compatible with base change along morphisms of test schemes) on each set $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} k$. Assume $L$ is commutative, and that $f$ satisfies the abelian-scheme property bundle: $f$ is smooth and proper, the fibre of $f$ over each point of $\operatorname{Spec} k$ is connected, and a relative group law on $f$ exists. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module, and assume the set of those $k$-points $x$ of $A$, i.e. sections $x$ of $f$ over $\mathrm{id}_{\operatorname{Spec} k}$, lying in the stabiliser of $\mathcal L$ — those for which the pullback of $\mathcal L$ along right multiplication by $x$ and the pullback of $\mathcal L$ along the first projection are locally isomorphic over the second projection — is finite. Let $M$ be an $\mathcal O_A$-module lying in $\mathrm{Pic}^0$: $M$ is invertible and for every $k$-point $x$ the pullback of $M$ along the translation $T_x$ determined by $L$ and $x$ is isomorphic to $M$. Then there is a $k$-point $x$ of $A$ and an isomorphism $M \otimes \mathcal L \cong T_x^{*}\mathcal L$.
--
--   This is Mumford's theorem that the map $x \mapsto T_x^{*}\mathcal L \otimes \mathcal L^{-1}$ from the $k$-points of an abelian variety onto $\mathrm{Pic}^0$ is surjective, here in the form in which ampleness of $\mathcal L$ is replaced by the finiteness of the $k$-points of its stabiliser $K(\mathcal L)$. It is used in the construction of symmetric elements of $\mathrm{Pic}^0$ and in the comparison of cohomological invariants of translates of $\mathcal L$ that feed into the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : (kernelPts f L 𝓛).Finite)
    (M : A.Modules) (hM : InPicZero f L M) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty (M ⊗ 𝓛 ≅ (Scheme.Modules.pullback (L.translate x)).obj 𝓛) := by sorry
