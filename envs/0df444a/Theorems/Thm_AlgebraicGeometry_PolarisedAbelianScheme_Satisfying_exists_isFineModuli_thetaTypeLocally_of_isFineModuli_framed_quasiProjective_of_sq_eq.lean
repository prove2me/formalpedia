-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/20093907-0b88-550e-b129-5fead3b75481
-- title:
--   Fine moduli for theta-type polarisations from framed moduli
-- statement:
--   Fix naturals $g,N,n$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, and assume $n \ge 3$. Let $B$ be a commutative ring in which $n$ and $N+1$ are units, and let $\zeta, \omega \in B$ satisfy $\zeta^{N+1}=1$, $1-\zeta^{j} \in B^{\times}$ for $0<j<N+1$, and $\omega^{2}=\zeta$. Let $\pi_H : H \to \operatorname{Spec} B$ be a scheme over $B$ together with an assignment $\mathrm{ptH}$ sending each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and each framed polarised abelian scheme of dimension $g$, degree $N+1$ and level $n$ over $S$ (a polarised abelian scheme with a $\operatorname{Proj}$ presentation of its polarisation module by $N+1$ sections forming a section basis on $\top$ and with closed-immersion associated morphism to $\mathbf{P}^{N}_{B}$) to a point of $H$ over $s$; assume this assignment makes $H$ a fine moduli scheme, i.e. it is invariant under isomorphism, compatible with pullback along ring maps over $\operatorname{Spec} B$, surjective on $s$-points, and injective up to isomorphism. Assume moreover that $\pi_H$ is separated, quasi-compact and locally of finite presentation, that every finite subset of $H$ lies in an affine open, and that $H$ is quasi-projective over $B$: there are $m$ and an immersion $H \to \operatorname{Proj}$ of the homogeneous polynomial ring in $m+1$ variables over $B$ whose composite with the structure morphism is $\pi_H$. Then there exist a scheme $M$, a morphism $\pi_M : M \to \operatorname{Spec} B$ and an assignment $\mathrm{pt}$ of $s$-points of $M$ to polarised abelian schemes of dimension $g$, degree $N+1$ and level $n$ satisfying the predicate $\mathtt{ThetaTypeLocally}\ \delta$ — namely: for every $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1}=1$ and $1-\zeta^{j}$ a unit for $0<j<N+1$, there is a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme $X'$ over $R'$ and a bijection $\mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$ such that the given object pulls back to $X'$ along $S \to R \to R'$ and $X'$ is theta-adapted for $\delta$ and that bijection — which makes $M$ a fine moduli scheme for these objects in the same four-part sense, and such that $\pi_M$ is separated, quasi-compact and locally of finite presentation, every finite subset of $M$ lies in an affine open, and $M$ is quasi-projective over $B$ in the same sense as $H$.
--
--   This is the passage from the moduli problem of framed (theta-rigidified) polarised abelian schemes to the moduli problem of polarised abelian schemes admitting a theta structure of type $\delta$ étale-locally, realised as a quotient of the framed moduli scheme by a finite group acting freely on framings, with the geometric finiteness properties (separatedness, quasi-compactness, local finite presentation, the affine-open property for finite sets, quasi-projectivity) carried along. It is used in the construction of the quasi-projective fine moduli scheme of theta-type polarised abelian schemes over such a base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (hn : 3 ≤ n) (B : Type) [CommRing B] (hn' : IsUnit ((n : ℕ) : B)) (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (ptH : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH)
    (hH : FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH)
    (hsep : IsSeparated πH) (hqc : QuasiCompact πH) (hfp : LocallyOfFinitePresentation πH)
    (hAF : ∀ F : Finset H, ∃ U : H.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : (∃ (qpm : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πH)) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) S → SchemeHomOver s πM),
      PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) M πM pt ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πM) := by sorry
