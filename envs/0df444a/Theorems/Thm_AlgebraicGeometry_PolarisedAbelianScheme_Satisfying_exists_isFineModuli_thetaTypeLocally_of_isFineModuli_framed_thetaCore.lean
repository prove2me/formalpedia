-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/5d1d4064-04a0-51f6-b384-b8fd37162fb9
-- title:
--   Fine moduli for ThetaTypeLocally from framed fine moduli
-- statement:
--   Fix natural numbers $g, N, n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$, and assume $n \ge 3$. Let $B$ be a commutative ring in which $n$ and $N+1$ are units, and let $\zeta \in B$ satisfy $\zeta^{N+1} = 1$ with $1 - \zeta^{j}$ a unit for all $0 < j < N+1$. Let $\pi_H : H \to \operatorname{Spec} B$ be a scheme over $B$ together with an assignment $\mathrm{pt}_H$ sending each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and each framed polarised abelian scheme $X$ of data $(g,N,n)$ over $S$ (a polarised abelian scheme of relative dimension $g$, degree $N+1$ and level $n$ together with a projective presentation of its polarisation module that is a closed immersion and whose sections form a section basis) to a morphism $\operatorname{Spec} S \to H$ over $s$; assume $\mathrm{pt}_H$ exhibits $H$ as a fine moduli scheme, i.e. it is constant on isomorphism classes, compatible with base change along ring maps over $B$, surjective on $S$-points over $s$, and injective up to isomorphism. Assume further that $\pi_H$ is separated, quasi-compact and locally of finite presentation, that every finite subset of $H$ lies in an affine open, and that $H$ is quasi-projective over $B$: some immersion $H \to \operatorname{Proj}$ of the graded polynomial algebra in $qpm+1$ variables over $B$, followed by the projection to $\operatorname{Spec} B$, equals $\pi_H$. Two further hypotheses are imposed. First, a closed theta-adapted locus: there are $H_\theta$ and a closed immersion $\iota : H_\theta \to H$, locally of finite presentation, such that for all $S$, $s$ and $X$ as above, $X$ is theta-adapted for $\delta, e$ (it carries a Schrödinger frame for its group law and polarisation whose sections are, via $e$, the pulled-back sections of its frame) if and only if $\mathrm{pt}_H\,S\,s\,X$ factors through $\iota$. Second, a torsor hypothesis: there are a finite group $\Gamma$ and an operation $\mathrm{act}$ on framed objects over each $(S,s)$ which leaves the underlying polarised abelian scheme unchanged, preserves theta-adaptedness, is isomorphic to the identity at $1$ and to the composite at products, respects isomorphism, is compatible with pullback along ring maps over $B$, acts freely on theta-adapted objects over nontrivial rings ($\mathrm{act}\,\gamma\,X \cong X$ forces $\gamma = 1$), and acts transitively locally: if $X, X'$ are theta-adapted with isomorphic underlying polarised abelian schemes, then there are finitely many $r_j \in S$ spanning the unit ideal such that over each $\mathrm{Localization.Away}(r_j)$ any pullbacks $Y$ of $X$ and $Y'$ of $X'$ satisfy $Y' \cong \mathrm{act}\,\gamma\,Y$ for some $\gamma \in \Gamma$. The conclusion asserts the existence of a scheme $M$, a morphism $\pi_M : M \to \operatorname{Spec} B$ and an assignment $\mathrm{pt}$ of $S$-points over $s$ to polarised abelian schemes of data $(g, N+1, n)$ over $S$ satisfying $\mathrm{ThetaTypeLocally}\ \delta$ (for every $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1}=1$ and $1-\zeta^{j}$ a unit for $0<j<N+1$, there is a faithfully flat étale $R$-algebra $R'$ over which the object becomes the underlying polarised abelian scheme of a theta-adapted framed object), such that $\mathrm{pt}$ exhibits $M$ as a fine moduli scheme for these objects, and $\pi_M$ is separated, quasi-compact and locally of finite presentation, every finite subset of $M$ lies in an affine open, and $M$ is quasi-projective over $B$ in the same sense as $H$.
--
--   This is the core step of the theta-structure construction of moduli of polarised abelian schemes with level structure: once the theta-adapted locus inside the framed moduli scheme is known to be closed and finitely presented, and the finite theta-level group is known to act freely and locally transitively on it, the quotient represents the functor of polarised abelian schemes admitting theta structures étale-locally. It is stated with those two inputs as hypotheses and is used in the variant that supplies them, [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_quasiProjective_of_sq_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore
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
    (hQP : (∃ (qpm : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πH))
    (hCLOSED : ∃ (Hθ : Scheme.{0}) (ι : Hθ ⟶ H), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
        ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X : FramedPolarisedAbelianScheme g N n S),
          X.IsThetaAdapted δ e ↔ ∃ y : Spec (CommRingCat.of S) ⟶ Hθ, y ≫ ι = (ptH S s X).1)
    (hTORSOR : ∃ (Γ : Type) (_ : Group Γ) (_ : Fintype Γ)
        (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) → Γ →
          FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S),
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
            (X : FramedPolarisedAbelianScheme g N n S),
            (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme) ∧
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
            (X : FramedPolarisedAbelianScheme g N n S),
            X.IsThetaAdapted δ e → (act S s γ X).IsThetaAdapted δ e) ∧
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
            (X : FramedPolarisedAbelianScheme g N n S),
            FramedPolarisedAbelianScheme.Iso (act S s 1 X) X) ∧
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ γ' : Γ)
            (X : FramedPolarisedAbelianScheme g N n S),
            FramedPolarisedAbelianScheme.Iso (act S s (γ * γ') X) (act S s γ (act S s γ' X))) ∧
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
            (X X' : FramedPolarisedAbelianScheme g N n S),
            FramedPolarisedAbelianScheme.Iso X X' → FramedPolarisedAbelianScheme.Iso (act S s γ X) (act S s γ X')) ∧
        (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
            (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
            Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
            ∀ (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
            FramedPolarisedAbelianScheme.IsPullback φ X X' → FramedPolarisedAbelianScheme.IsPullback φ (act S s γ X) (act S' s' γ X')) ∧
        (∀ (S : Type) [CommRing S] [Nontrivial S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
            (X : FramedPolarisedAbelianScheme g N n S),
            X.IsThetaAdapted δ e → FramedPolarisedAbelianScheme.Iso (act S s γ X) X → γ = 1) ∧
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
            (X X' : FramedPolarisedAbelianScheme g N n S),
            X.IsThetaAdapted δ e → X'.IsThetaAdapted δ e →
            PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme →
            ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
              (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
              FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
              FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
              ∃ γ : Γ, FramedPolarisedAbelianScheme.Iso
                (act (Localization.Away (r j)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) ≫ s) γ Y) Y')) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) S → SchemeHomOver s πM),
      PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n (PolarisedAbelianScheme.ThetaTypeLocally δ) M πM pt ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πM) := by sorry
