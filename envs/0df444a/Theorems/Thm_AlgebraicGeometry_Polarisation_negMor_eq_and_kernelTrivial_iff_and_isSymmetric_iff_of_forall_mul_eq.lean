-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq
-- name    : AlgebraicGeometry.Polarisation.negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/037c49e9-ba89-54bc-b06f-1433c635bb22
-- title:
--   Equal multiplications force equal unit, negation, kernel and symmetry
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism, and let $L'$, $L''$ be two relative group laws on $f$, i.e. two structures assigning to every scheme $T$ and every $t\colon T\to\operatorname{Spec}S$ a multiplication, unit and inversion on the set $\{\varphi\colon T\to A \mid \varphi\text{ followed by }f = t\}$ of $T$-points of $A$ over $t$, subject to the group axioms and naturality of the multiplication in $T$. Assume the two multiplications literally coincide: for all $T$, all $t$ and all points $P,Q$ over $t$, $L'.\mathrm{mul}\,t\,P\,Q = L''.\mathrm{mul}\,t\,P\,Q$. The conclusion is a conjunction of four assertions. First, $\mathtt{negMor}\,f\,L' = \mathtt{negMor}\,f\,L''$ as morphisms $A\to A$, where $\mathtt{negMor}\,f\,L$ is the underlying morphism of the $L$-inverse of the tautological point $\mathrm{id}_A$ over $f$. Second, the units agree: $L'.\mathrm{one}\,t = L''.\mathrm{one}\,t$ for every $T$ and every $t\colon T\to\operatorname{Spec}S$. Third, for every module $\mathcal M$ on $A$, the predicate $\mathtt{KernelTrivial}\,f\,L'\,\mathcal M$ holds if and only if $\mathtt{KernelTrivial}\,f\,L''\,\mathcal M$ does; here $\mathtt{KernelTrivial}\,f\,L\,\mathcal M$ says that for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}S$ and every point $x$ of $A$ over $t$, if the pullback along the slice morphism $\mathtt{sliceAt}\,f\,x\colon A\times_{\operatorname{Spec}S}\operatorname{Spec}R\to A\times_{\operatorname{Spec}S}A$ of the Mumford bundle $m^*\mathcal M\otimes p_1^*\mathcal M^\vee\otimes p_2^*\mathcal M^\vee$ (with $m$ the addition morphism of $L$) is isomorphic to the unit module locally over the base $\operatorname{Spec}R$, then $x = L.\mathrm{one}\,t$. Fourth, for every module $\mathcal M$ on $A$, symmetry for $L'$ is equivalent to symmetry for $L''$, where symmetry means that $\mathcal M$ and its pullback along the negation morphism become isomorphic over the preimages $f^{-1}(U)$ of a family of opens $U$ covering $\operatorname{Spec}S$.
--
--   A transport lemma: the unit, the inversion, the negation and addition morphisms, the Mumford bundle, and hence the conditions '$K(\mathcal M)$ is trivial' and '$[-1]^*\mathcal M\cong\mathcal M$ locally on the base', depend on a relative group law only through its multiplication. It is used to move symmetry and principal-square-root statements between two presentations of the same group law, in the construction of symmetric principal square roots after a finite faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L' L'' : RelativeGroupLaw S f)
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      L'.mul t P Q = L''.mul t P Q) :
    negMor f L' = negMor f L'' ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)), L'.one t = L''.one t) ∧
    (∀ 𝓜 : A.Modules, KernelTrivial f L' 𝓜 ↔ KernelTrivial f L'' 𝓜) ∧
    (∀ 𝓜 : A.Modules, IsSymmetric f L' 𝓜 ↔ IsSymmetric f L'' 𝓜) := by sorry
