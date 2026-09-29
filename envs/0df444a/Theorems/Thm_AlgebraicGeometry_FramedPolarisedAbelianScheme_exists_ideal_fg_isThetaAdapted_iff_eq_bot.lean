-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_isThetaAdapted_iff_eq_bot
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/9623e269-602d-5394-94f1-385c5a7b8615
-- title:
--   A functorial finitely generated ideal cutting out theta-adaptedness
-- statement:
--   Fix natural numbers $g, N, n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all entries nonzero and $\prod_i \delta_i = N+1$, together with a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$. Fix a commutative ring $B$ in which $N+1$ is invertible and an element $\zeta \in B$ with $\zeta^{N+1} = 1$ and $1 - \zeta^j$ a unit for all $0 < j < N+1$. The assertion is the existence of an assignment $I$ which, for every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every framed polarised abelian scheme $X$ of type $(g, N, n)$ over $S$ — that is, an abelian scheme $A \to \operatorname{Spec} S$ with commutative relative group law, fibres of dimension $g$, $2g$ marked $n$-torsion sections freely generating the $n$-torsion on geometric fibres, an invertible module `pol` which is very ample with geometric fibre $H^0$ of rank $N+1$, and a `ProjPresentation` of `pol` by $N+1$ global sections whose induced morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis — produces an ideal $I(S, s, X) \subseteq S$ such that: (i) $I(S,s,X)$ is finitely generated; (ii) $I(S,s,X) = I(S,s,X')$ whenever $X$ and $X'$ are isomorphic as framed polarised abelian schemes, i.e. related by an isomorphism of the underlying schemes over $S$ compatible with the group laws, the marked points, the morphisms to $\mathbb{P}^N_S$ and, locally on the base, the polarisation modules; (iii) if $\varphi : S \to S'$ is a ring homomorphism with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and $X'$ over $S'$ is a pullback of $X$ along $\varphi$ in the framed polarised sense (a fibre-product diagram compatible with group laws, marked sections, polarisation and the frames, over the base-change map of projective spaces), then $I(S', s', X') = \varphi(I(S,s,X))S'$; and (iv) $X$ is theta-adapted for $(\delta, e)$ — there is a Schrödinger frame for $(X.f, X.L, X.\mathrm{pol})$ over the identity base with multidegree $\delta$ whose section indexed by $e(i)$ is the pullback of the $i$-th frame section — if and only if $I(S,s,X) = 0$.
--
--   This is the ideal-theoretic form of the statement that theta-adaptedness of a framed polarised abelian scheme is a closed condition on the base, cut out functorially in the base by a finitely generated ideal; it packages Mumford's theta-relation formalism into a descent-compatible vanishing criterion. It is used to derive the equivalence between the frame morphism being a closed immersion and theta-adaptedness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_isThetaAdapted_iff_eq_bot.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
    ∃ I : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) →
        FramedPolarisedAbelianScheme g N n S → Ideal S,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X : FramedPolarisedAbelianScheme g N n S), (I S s X).FG) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X X' : FramedPolarisedAbelianScheme g N n S),
          FramedPolarisedAbelianScheme.Iso X X' → I S s X = I S s X') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
          Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
          ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
          FramedPolarisedAbelianScheme.IsPullback φ X X' → I S' s' X' = (I S s X).map φ) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X : FramedPolarisedAbelianScheme g N n S), X.IsThetaAdapted δ e ↔ I S s X = ⊥) := by sorry
