-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/71bc19a5-bba8-58f9-be6e-f8ef2c508dd5
-- title:
--   Trivial Mumford kernel is stable under base change
-- statement:
--   Let $\varphi : S \to S'$ be a homomorphism of commutative rings, let $A, A'$ be schemes, let $f : A \to \operatorname{Spec} S$, $f' : A' \to \operatorname{Spec} S'$ and $g : A' \to A$ be morphisms, and assume the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}\varphi$ is cartesian. Let $L$ be a relative group law on $f$ and $L'$ one on $f'$, i.e. functorial group structures on the sets $\{\psi : T \to A \mid \psi \circ f = t\}$ of points over a base morphism $t$. Assume $g$ is multiplicative on points: for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all points $P, Q$ of $A'$ over $t'$, the $L'$-product of $P$ and $Q$ followed by $g$ equals the $L$-product, over $t'$ followed by $\operatorname{Spec}\varphi$, of $P$ followed by $g$ and $Q$ followed by $g$. Let $\mathcal{L}$ be a module on $A$ which is invertible (every point of $A$ has an open neighbourhood on which $\mathcal{L}$ pulls back to the unit module) and satisfies `KernelTrivial f L 𝓛`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $A$ over $t$, if the pullback along $\mathrm{sliceAt}\,f\,x$ of the Mumford bundle $m^*\mathcal{L} \otimes (\mathrm{pr}_1^*\mathcal{L}^{\vee} \otimes \mathrm{pr}_2^*\mathcal{L}^{\vee})$ on $A \times_S A$ is, locally on $\operatorname{Spec} R$ (over the structure map $A \times_S \operatorname{Spec} R \to \operatorname{Spec} R$), isomorphic to the unit module, then $x$ is the $L$-identity over $t$. Then the same condition `KernelTrivial` holds for $f'$, $L'$ and $g^*\mathcal{L}$.
--
--   This is the base-change stability of the condition $K(\mathcal{L}) = e$ on a polarisation, stated in the functor-of-points form used throughout the treatment of Mumford bundles and the Rosati involution. It is invoked when a principal square root of a polarisation is descended or produced over a field or a discrete valuation ring, and in the analysis of the two-torsion of the kernel over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback g).obj 𝓛) := by sorry
