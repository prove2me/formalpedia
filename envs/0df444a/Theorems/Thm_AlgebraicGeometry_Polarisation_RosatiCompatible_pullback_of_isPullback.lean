-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/ea9f8ea0-5024-52ea-9327-069abe13afca
-- title:
--   Rosati compatibility is stable under cartesian base change
-- statement:
--   Let $S$ and $S'$ be commutative rings and $\varphi : S \to S'$ a ring homomorphism. Let $f : A \to \operatorname{Spec} S$ carry a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points over the base, with associativity, unit and inverse laws and naturality in $T$), and likewise $f' : A' \to \operatorname{Spec} S'$ with $L'$. Let $g : A' \to A$ make the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}\varphi$ cartesian, and assume $g$ is a homomorphism on points: for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P, Q : T \to A'$ over $t'$, the composite of $L'$-multiplication of $P$ and $Q$ with $g$ equals the $L$-multiplication, over $t'$ followed by $\operatorname{Spec}\varphi$, of $P$ followed by $g$ and $Q$ followed by $g$. Let $I$ be a type, $\iota : I \to (A \to A)$ and $\iota' : I \to (A' \to A')$ families of endomorphisms over the respective bases ($\iota b$ followed by $f$ is $f$, and $\iota' b$ followed by $f'$ is $f'$), with $\iota' b$ followed by $g$ equal to $g$ followed by $\iota b$ for each $b$, and let $\star : I \to I$. Let $\mathcal L$ be an invertible $\mathcal O_A$-module, i.e. every point of $A$ has an open neighbourhood on which $\mathcal L$ pulls back to the unit module. Write $\Lambda(\mathcal M) = \mu^{*}\mathcal M \otimes (p_1^{*}\mathcal M^{\vee} \otimes p_2^{*}\mathcal M^{\vee})$ for the Mumford bundle on the fibre square, $\mu$ being the addition morphism of the group law. Assume that for each $b \in I$ the pullbacks of $\Lambda(\mathcal L)$ along $(p_1, p_2 \circ \iota b)$ and along $(p_1 \circ \iota(\star b), p_2)$ are isomorphic locally on the base, meaning that every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic. Then the same holds for $f'$, $L'$, the pullback $g^{*}\mathcal L$, the family $\iota'$ and the same involution datum $\star$.
--
--   This is the base-change statement for the Mumford-bundle condition expressing that $\iota(\star b)$ is the Rosati adjoint of $\iota(b)$ relative to the polarisation $\mathcal L$: the condition descends along any cartesian square of relative group laws whose base-change morphism is a homomorphism on points and intertwines the two endomorphism families. It is used in the construction and comparison of polarised abelian schemes with quaternionic multiplication (fake elliptic curves) over varying bases in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_of_isPullback
    (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (f' : A' ⟶ Spec (CommRingCat.of S')) (L' : RelativeGroupLaw S' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {I : Type} (ι : I → (A ⟶ A)) (hι : ∀ b, ι b ≫ f = f) (ι' : I → (A' ⟶ A')) (hι' : ∀ b, ι' b ≫ f' = f')
    (hgι : ∀ b, ι' b ≫ g = g ≫ ι b) (star : I → I)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hros : RosatiCompatible f L 𝓛 ι hι star) :
    RosatiCompatible f' L' ((Scheme.Modules.pullback g).obj 𝓛) ι' hι' star := by sorry
