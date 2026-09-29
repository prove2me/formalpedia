-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_monoidHom_aut_forall_pt_act_eq_of_isFineModuli
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_monoidHom_aut_forall_pt_act_eq_of_isFineModuli
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/4419dfda-9694-5763-86df-b045980e1aad
-- title:
--   Functorial Γ-action descends to automorphisms of a fine moduli scheme
-- statement:
--   Fix naturals $g,N,n$ and a commutative ring $B$, and let $\Theta$ be a predicate on framed polarised abelian schemes over an arbitrary commutative ring $S$ — objects consisting of an abelian scheme of relative fibre dimension $g$ over $\operatorname{Spec} S$ with commutative relative group law, $2g$ sections of exact order dividing $n$ that are independent and span the $n$-torsion on geometric fibres, an invertible very ample module `pol` with geometric fibre $H^0$ of rank $N+1$, together with a projective presentation of `pol` by $N+1$ sections whose associated morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis. Let $\pi_\Theta : H_\Theta \to \operatorname{Spec} B$ be a separated morphism of schemes and let $\mathrm{pt}_\Theta$ attach to every $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every $X$ over $S$ with $\Theta\,S\,X$ a morphism $\operatorname{Spec} S \to H_\Theta$ with composite $s$, subject to: invariance under framed isomorphism (isomorphism of the total spaces over $\operatorname{Spec} S$ compatible with the group law, the torsion sections, the frame morphism to $\mathbb{P}^N_S$, and locally on the base with the polarisation); compatibility with base change, i.e. if $\operatorname{Spec}\varphi$ followed by $s$ equals $s'$ and $X'$ over $S'$ is a pullback of $X$ along $\varphi : S \to S'$ then $\mathrm{pt}_\Theta(X')$ equals $\mathrm{pt}_\Theta(X) \circ \operatorname{Spec}\varphi$; surjectivity onto all $S$-points of $H_\Theta$ over $s$; and injectivity up to framed isomorphism. Let $\Gamma$ be a group acting, for each $S$ and each $s$, on framed objects over $S$ by $X \mapsto \mathrm{act}\,S\,s\,\gamma\,X$, such that the action leaves the underlying polarised abelian scheme untouched, preserves $\Theta$, is unital and multiplicative up to framed isomorphism, sends framed isomorphisms to framed isomorphisms, and carries pullback squares along $\varphi$ to pullback squares. Assume further that $\Theta$ is invariant under framed isomorphism and under pullback, and that for every ring homomorphism $\varphi : S \to S'$ and every framed object over $S$ some pullback along $\varphi$ exists. Then there is a group homomorphism $\rho : \Gamma \to \operatorname{Aut} H_\Theta$ such that each $\rho(\gamma)$ is a morphism over $B$, i.e. $\rho(\gamma)$ followed by $\pi_\Theta$ is $\pi_\Theta$, and such that for all $S$, $s$, $\gamma$ and all $X$ with $\Theta\,S\,X$ one has $\mathrm{pt}_\Theta(\gamma \cdot X) = \rho(\gamma) \circ \mathrm{pt}_\Theta(X)$.
--
--   This is the Yoneda-style passage from a functorial group action on the objects classified by a fine moduli scheme (fineness being expressed here by the stated surjectivity and injectivity of $\mathrm{pt}_\Theta$ on affine points, together with its compatibility with isomorphisms and base change) to an honest action of $\Gamma$ by automorphisms of the moduli scheme over the base. It is used in the construction of the moduli scheme attached to the local $\Theta$-type condition from the moduli scheme for framed objects, via [`AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver`](thm.html#AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver), which produces a morphism of schemes from a base-change-compatible assignment on affine points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_monoidHom_aut_forall_pt_act_eq_of_isFineModuli.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_monoidHom_aut_forall_pt_act_eq_of_isFineModuli
    (g N n : ℕ) (B : Type) [CommRing B]
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (HΘ : Scheme.{0}) (πΘ : HΘ ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πΘ)
    (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s πΘ)
    (hpt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
      FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX')
    (hpt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' →
      (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1)
    (hpt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πΘ),
      ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x)
    (hpt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
      FramedPolarisedAbelianScheme.Iso X X')
    (Γ : Type) [Group Γ]
    (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) →
      Γ → FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S)
    (hact_val : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
      (X : FramedPolarisedAbelianScheme g N n S), (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme)
    (hactΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S (act S s γ X))
    (hact_one : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S), FramedPolarisedAbelianScheme.Iso (act S s 1 X) X)
    (hact_mul : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ γ' : Γ)
      (X : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso (act S s (γ * γ') X) (act S s γ (act S s γ' X)))
    (hact_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
      (X X' : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso X X' → FramedPolarisedAbelianScheme.Iso (act S s γ X) (act S s γ X'))
    (hact_bc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' → FramedPolarisedAbelianScheme.IsPullback φ (act S s γ X) (act S' s' γ X'))
    (hΘiso : ∀ (S : Type) [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso X X' → Θ S X → Θ S X')
    (hΘbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (φ : S →+* S')
      (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' → Θ S X → Θ S' X')
    (hΘBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (X : FramedPolarisedAbelianScheme g N n S),
      ∃ X' : FramedPolarisedAbelianScheme g N n S', FramedPolarisedAbelianScheme.IsPullback φ X X') :
    ∃ ρ : Γ →* Aut HΘ, (∀ γ : Γ, (ρ γ).hom ≫ πΘ = πΘ) ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X),
        (ptΘ S s (act S s γ X) (hactΘ S s γ X hX)).1 = (ptΘ S s X hX).1 ≫ (ρ γ).hom := by sorry
