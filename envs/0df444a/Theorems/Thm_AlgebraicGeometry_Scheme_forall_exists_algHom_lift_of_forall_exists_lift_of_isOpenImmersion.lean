-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion
-- name    : AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/669c5b38-6b15-5179-8867-a8eb4897105c
-- title:
--   Scheme-level Artinian lifting restricts to ring-level lifting on an affine chart
-- statement:
--   Let $R$ be a commutative ring and let $\varpi : M \to \operatorname{Spec} R$ be a morphism from a scheme $M$ (everything in the bottom universe). Let $n \in \mathbb{N}$, let $I$ be an ideal of $P = R[x_1,\dots,x_n] =$ `MvPolynomial (Fin n) R`, and let $\iota : \operatorname{Spec}(P/I) \to M$ be an open immersion which is a morphism over $\operatorname{Spec} R$, in the sense that $\iota$ followed by $\varpi$ equals $\operatorname{Spec}$ of the structure map $R \to P/I$. Assume the scheme-level lifting hypothesis $h$: for all rings $T'$, $T$, with $T'$ local and Artinian whose residue field is algebraically closed of characteristic $\ell$ for some prime $\ell$, and $T$ nontrivial, for every surjective ring homomorphism $p : T' \to T$ with $\ker(p)\cdot \mathfrak{m}_{T'} = 0$, and for all $s : \operatorname{Spec} T' \to \operatorname{Spec} R$ and $m : \operatorname{Spec} T \to M$ with $m$ followed by $\varpi$ equal to $\operatorname{Spec}(p)$ followed by $s$, there is $m' : \operatorname{Spec} T' \to M$ lying over $s$ with $\operatorname{Spec}(p)$ followed by $m'$ equal to $m$. The conclusion is the corresponding ring-level statement for $P/I$: for all $T'$, $T$ as above, now equipped with $R$-algebra structures, every surjective $R$-algebra map $p : T' \to T$ with $\ker(p)\cdot \mathfrak{m}_{T'} = 0$ and every $R$-algebra map $m : P/I \to T$ admit an $R$-algebra map $m' : P/I \to T'$ with $p \circ m' = m$.
--
--   This is the passage from the infinitesimal lifting property of $M$ over $\operatorname{Spec} R$ against small surjections of Artinian local rings with algebraically closed residue field of positive characteristic to the same property for the coordinate ring of an affine open chart of $M$ of finite type over $R$. It is used in the verification of smoothness of $M$ via such a lifting criterion, in [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion
    {R : Type} [CommRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R))
    (ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M) [IsOpenImmersion ι]
    (hι : ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))))
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m := by sorry
