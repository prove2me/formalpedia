-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isClosedImmersion_iff_isThetaAdapted
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isClosedImmersion_iff_isThetaAdapted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ae5d29a4-fbbe-58d7-94d5-804a9becd838
-- title:
--   The theta-adapted locus is closed and finitely presented in H
-- statement:
--   Fix natural numbers $g$, $N$, $n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with each $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, and a bijection $e$ from $\mathrm{Fin}(N+1)$ onto $\prod_i \mathbb{Z}/\delta_i$. Let $n \ge 3$ and let $B$ be a commutative ring in which $n$ and $N+1$ are units, equipped with $\zeta \in B$ satisfying $\zeta^{N+1}=1$ and $1-\zeta^{j} \in B^{\times}$ for $0<j<N+1$. Let $H$ be a scheme with a morphism $\pi_H : H \to \operatorname{Spec} B$ and let $\mathrm{pt}_H$ assign, to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every framed polarised abelian scheme $X$ of dimension $g$, degree $N+1$ and level $n$ over $S$ (a polarised abelian scheme with a projective presentation of its polarisation by $N+1$ global sections whose associated morphism to projective $N$-space is a closed immersion and whose sections form a section basis), a morphism $\operatorname{Spec} S \to H$ over $s$; assume $(H,\pi_H,\mathrm{pt}_H)$ is a fine moduli datum, i.e. $\mathrm{pt}_H$ is invariant under isomorphism, compatible with base change along ring maps and pullback of framed objects, surjective on $S$-points over $\operatorname{Spec} B$ and injective up to isomorphism. Assume further that $\pi_H$ is separated, quasi-compact and locally of finite presentation, that every finite subset of $H$ lies in an affine open, and that $H$ admits an immersion into some projective space $\mathbb{P}^{qpm}_B$ compatible with the projections to $\operatorname{Spec} B$. Then there exist a scheme $H_\theta$ and a morphism $\iota : H_\theta \to H$ which is a closed immersion and locally of finite presentation, such that for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every framed polarised abelian scheme $X$ over $S$, the object $X$ is theta-adapted for $(\delta,e)$ — there is a Schrödinger frame for $X$ relative to the identity base, with sections indexed by $\prod_i \mathbb{Z}/\delta_i$ forming a basis and carrying lifts of group elements and of additive characters acting by translation and by scalars, whose section at $e(i)$ is the pullback of the $i$-th frame section of $X$ for every $i$ — if and only if the morphism underlying $\mathrm{pt}_H(S,s,X)$ factors through $\iota$.
--
--   This realises the theta-adapted sub-functor of the moduli of framed polarised abelian schemes (those whose frame is a Schrödinger frame for the type $\delta$) as a closed, locally finitely presented subscheme $H_\theta$ of the framed moduli scheme $H$. It is the step that allows moduli with theta structures of type $\delta$ to be constructed from framed moduli, and is used in the construction of fine moduli for polarised abelian schemes of a given theta type locally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isClosedImmersion_iff_isThetaAdapted.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isClosedImmersion_iff_isThetaAdapted
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (hn : 3 ≤ n) (B : Type) [CommRing B] (hn' : IsUnit ((n : ℕ) : B)) (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (ptH : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH)
    (hH : FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH)
    (hsep : IsSeparated πH) (hqc : QuasiCompact πH) (hfp : LocallyOfFinitePresentation πH)
    (hAF : ∀ F : Finset H, ∃ U : H.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : (∃ (qpm : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πH)) :
    ∃ (Hθ : Scheme.{0}) (ι : Hθ ⟶ H), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : FramedPolarisedAbelianScheme g N n S),
        X.IsThetaAdapted δ e ↔ ∃ y : Spec (CommRingCat.of S) ⟶ Hθ, y ≫ ι = (ptH S s X).1 := by sorry
