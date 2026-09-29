-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_isPullback_of_kernelTrivial_of_locIsoOnBase_of_isAlgClosed
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_isPullback_of_kernelTrivial_of_locIsoOnBase_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/6360b618-bfa1-5193-afe7-1afea30924ad
-- title:
--   Mumford kernel of g^*L equals the 2-torsion
-- statement:
--   Let $S$ be a commutative ring, $f\colon A\to\operatorname{Spec}S$ a morphism of schemes, and $L$ a `RelativeGroupLaw` for $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of sections over $S$-schemes $(T,t)$, compatible with base change along $T'\to T$. Assume $f$ satisfies `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be an invertible module on $A$ (locally on $A$ isomorphic to the unit module). Let $W$ be an $S$-algebra and let $\tau$ be an invertible module on $A_W=A\times_{\operatorname{Spec}S}\operatorname{Spec}W$ such that, for the group law $L$ base-changed to $W$: (i) the Mumford kernel of $\tau$ is trivial, i.e. for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}W$ and every point $x$ of $A_W$ over $t$, if the restriction along `sliceAt` of the Mumford bundle $m^*\tau\otimes(\mathrm{pr}_1^*\tau^\vee\otimes \mathrm{pr}_2^*\tau^\vee)$ is isomorphic to the unit module locally over the points of $\operatorname{Spec}R$, then $x$ is the identity section; and (ii) the pullback of $\mathcal L$ to $A_W$ along the first projection is isomorphic to $\tau\otimes[-1]^*\tau$ locally over the points of $\operatorname{Spec}W$, where $[-1]$ is the inversion morphism of the base-changed law. Let $k$ be an algebraically closed field which is an $S$-algebra and a $W$-algebra, compatibly. Let $f'\colon A'\to\operatorname{Spec}k$ and $g\colon A'\to A$ form a cartesian square over $\operatorname{Spec}k\to\operatorname{Spec}S$, and let $L'$ be a relative group law for $f'$ such that $g$ is multiplicative: for all $T$, $t'\colon T\to\operatorname{Spec}k$ and points $P,Q$ of $f'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,P\,Q$ with $g$ equals the $L$-product of $P\circ g$ and $Q\circ g$ over $t'$ followed by $\operatorname{Spec}(S\to k)$. Then $g^*\mathcal L$ has `KernelIsTwoTorsion`: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}k$ and every point $x$ of $A'$ over $t$, the restriction along `sliceAt` of the Mumford bundle of $g^*\mathcal L$ is isomorphic to the unit module locally over the points of $\operatorname{Spec}R$ if and only if $x+x$ is the identity section.
--
--   This is the functor-of-points form of the classical statement that the Mumford kernel $K(\mathcal M)$ of a symmetrisation $\mathcal M=\tau\otimes[-1]^*\tau$ of a bundle with trivial kernel is exactly the $2$-torsion subgroup, here transported to a geometric fibre over an algebraically closed field $k$ which is reached through the auxiliary algebra $W$ over which $\mathcal L$ becomes such a symmetrisation. It feeds the criterion [`GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat) for triviality of the kernel of a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_isPullback_of_kernelTrivial_of_locIsoOnBase_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_isPullback_of_kernelTrivial_of_locIsoOnBase_of_isAlgClosed
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (W : Type) [CommRing W] [Algebra S W]
    (τ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules) (hτ : Scheme.Modules.IsInvertible τ)
    (hKτ : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))) τ)
    (hrτ : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
      (τ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))))).obj τ))
    (k : Type) [Field k] [IsAlgClosed k] [Algebra S k] [Algebra W k] [IsScalarTower S W k]
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S k))))
    (L' : RelativeGroupLaw k f')
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S k)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback g).obj 𝓛) := by sorry
