-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_quasiProjective
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_quasiProjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/d1f9696a-23e0-55f6-ac63-9ce804ccb517
-- title:
--   Quasi-projective fine moduli of polarised abelian schemes of theta type δ
-- statement:
--   Fix natural numbers $g, N, n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, assume $n \ge 3$, and let $\mathcal{O}$ be a commutative ring in which both $n$ and $N+1$ are units. The moduli problem in question attaches to a commutative ring $S$ the structures `PolarisedAbelianScheme.Satisfying g (N+1) n (ThetaTypeLocally δ) S`, namely a datum $u$ consisting of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law on $f$, the property bundle `AbelianSchemePropertyBundle`, all fibres of topological Krull dimension $g$, sections $P_1,\dots,P_{2g}$ over $S$ killed by $n$ which on every geometric fibre generate the $n$-torsion freely as $(\mathbb{Z}/n)^{2g}$, and an invertible module `pol` which is a closed immersion by sections over $\operatorname{Spec} S$ and whose geometric fibre $H^0$ has rank $N+1$, together with a proof that $u$ is of theta type $\delta$ étale-locally: for every $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1-\zeta^{j}$ a unit for $0 < j < N+1$, there is a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme $X'$ over $R'$ (a polarised abelian scheme together with a projective presentation of `pol` in $\mathbb{P}^N$ whose associated morphism is a closed immersion and whose sections form a section basis), and a bijection $\mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$, such that $u$ pulls back to $X'$ along $S \to R \to R'$ and $X'$ is theta-adapted for $\delta$ and that bijection. The assertion is that there exist a scheme $M$, a morphism $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ and an assignment $\mathrm{pt}$ sending, for each commutative ring $S$ and each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, such a structure over $S$ to an $s$-point of $M$, with: $\mathrm{pt}$ constant on isomorphism classes, compatible with pullback along ring homomorphisms over $\operatorname{Spec}\mathcal{O}$, surjective onto $s$-points of $M$ and injective up to isomorphism (i.e. $(M,\pi_M,\mathrm{pt})$ is a fine moduli scheme); $\pi_M$ separated, quasi-compact and locally of finite presentation; every finite subset of $M$ contained in an affine open; and some $q \in \mathbb{N}$ and an immersion $\iota : M \to \operatorname{Proj}$ of the homogeneous coordinate ring in $q+1$ variables over $\mathcal{O}$ with $\iota$ followed by the structure morphism of $\mathbb{P}^{q}_{\mathcal{O}}$ equal to $\pi_M$.
--
--   This is the representability statement for polarised abelian schemes of relative dimension $g$ and degree $N+1$ with full level-$n$ structure which acquire a theta structure of type $\delta$ étale-locally, in the quasi-projective form needed for later geometric work; the moduli scheme is constructed over an arbitrary base ring in which $n$ and $N+1$ are invertible. It is used in the construction of fine moduli spaces for the quaternionic (Čerednik–Drinfeld) setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_quasiProjective.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_quasiProjective
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (hn : 3 ≤ n) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪)) (hd : IsUnit ((N + 1 : ℕ) : 𝒪)) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) S → SchemeHomOver s πM),
      PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) M πM pt ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM) := by sorry
