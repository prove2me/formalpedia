-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_eq_one_of_locIsoOnBase_sliceAt_mumfordBundle_of_kernelTrivial_pullback_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.eq_one_of_locIsoOnBase_sliceAt_mumfordBundle_of_kernelTrivial_pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/6089dfb5-36a8-50c1-8c14-4f6102ad1097
-- title:
--   Kernel triviality upstairs forces x=e on S'-test points
-- statement:
--   Let $\varphi\colon S\to S'$ be a homomorphism of commutative rings, let $f\colon A\to\operatorname{Spec}S$ and $f'\colon A'\to\operatorname{Spec}S'$ be morphisms of schemes, and let $g\colon A'\to A$ make the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}\varphi$ cartesian. Let $L$, $L'$ be relative group laws on the functors of points of $f$, $f'$ (functorial multiplication, unit and inverse satisfying the group axioms, with multiplication compatible with base change of the test scheme), assumed compatible in the sense that for every scheme $T$, every $t'\colon T\to\operatorname{Spec}S'$ and all $P,Q\colon T\to A'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,P\,Q$ with $g$ equals $L.\mathrm{mul}$ at $t'$ followed by $\operatorname{Spec}\varphi$ applied to $P\circ g$ and $Q\circ g$. Let $\mathcal L$ be an invertible $\mathcal O_A$-module, and assume `KernelTrivial` for $f'$, $L'$ and $g^*\mathcal L$: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}S'$ and every $x'\colon\operatorname{Spec}R\to A'$ over $t$, if the pullback along the slice $(\mathrm{pr}_1,\mathrm{pr}_2\circ x')$ of the Mumford bundle $\mu^*(g^*\mathcal L)\otimes(\mathrm{pr}_1^*(g^*\mathcal L)^\vee\otimes \mathrm{pr}_2^*(g^*\mathcal L)^\vee)$ becomes isomorphic to the unit module over the preimage of some open neighbourhood of each point of $\operatorname{Spec}R$, then $x'$ is the unit section. Then, for every commutative ring $T$, every $t'\colon\operatorname{Spec}T\to\operatorname{Spec}S'$ and every $x\colon\operatorname{Spec}T\to A$ with $x$ followed by $f$ equal to $t'$ followed by $\operatorname{Spec}\varphi$, local triviality on $\operatorname{Spec}T$ in the same sense of the pullback of the Mumford bundle of $\mathcal L$ along the slice at $x$ implies $x=L.\mathrm{one}$ at $t'$ followed by $\operatorname{Spec}\varphi$.
--
--   This is the transfer of Mumford's condition $K(\mathcal L)=e$ along a cartesian base change $\operatorname{Spec}S'\to\operatorname{Spec}S$: triviality of the kernel of the polarisation bundle upstairs yields triviality of the kernel on all test points of $A$ that factor through the base change, with no flatness, finiteness or Noetherian hypothesis on $\varphi$. It is used in the reduction of kernel triviality for an abelian scheme to the corresponding statement on geometric fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_eq_one_of_locIsoOnBase_sliceAt_mumfordBundle_of_kernelTrivial_pullback_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.eq_one_of_locIsoOnBase_sliceAt_mumfordBundle_of_kernelTrivial_pullback_of_isPullback
    {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : KernelTrivial f' L' ((Scheme.Modules.pullback g).obj 𝓛))
    (T : Type u) [CommRing T] (t' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S'))
    (x : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f)
    (hx : LocIsoOnBase (pullback.snd f (t' ≫ Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ _)) :
    x = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by sorry
