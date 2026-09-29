-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed
-- name    : AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b3eef879-4ad7-5c03-94d0-3b5f9e8804c1
-- title:
--   Scheme-level Artinian lifting descends to chart algebras
-- statement:
--   Let $R$ be a commutative ring, $M$ a scheme (all in universe $0$), and $\varpi\colon M\to\operatorname{Spec}R$ a morphism. Fix $n\in\mathbb N$, write $P=R[x_0,\dots,x_{n-1}]$ for the polynomial ring `MvPolynomial (Fin n) R`, let $I\subseteq P$ be an ideal, and let $\iota\colon\operatorname{Spec}(P/I)\to M$ be an open immersion whose composite with $\varpi$ is $\operatorname{Spec}$ of the structure map $R\to P/I$. Assume the scheme-level lifting hypothesis: for all types $T',T$ with $T'$ an Artinian local ring whose residue field is algebraically closed and $T$ a nontrivial commutative ring, every surjective ring homomorphism $p\colon T'\to T$ with $\ker p\cdot\mathfrak m_{T'}=0$, every morphism $s\colon\operatorname{Spec}T'\to\operatorname{Spec}R$ and every $m\colon\operatorname{Spec}T\to M$ with $m$ followed by $\varpi$ equal to $\operatorname{Spec}p$ followed by $s$, admit $m'\colon\operatorname{Spec}T'\to M$ with $m'$ followed by $\varpi$ equal to $s$ and $\operatorname{Spec}p$ followed by $m'$ equal to $m$. The conclusion is the corresponding algebra-level statement: for all such $T',T$ carrying $R$-algebra structures and every surjective $R$-algebra map $p\colon T'\to T$ with $\ker p\cdot\mathfrak m_{T'}=0$, every $R$-algebra map $m\colon P/I\to T$ factors as $p\circ m'$ for some $R$-algebra map $m'\colon P/I\to T'$.
--
--   This transfers the infinitesimal lifting property along small surjections of Artinian local rings with algebraically closed residue field from a morphism of schemes $\varpi\colon M\to\operatorname{Spec}R$ to the $R$-algebra $P/I$ of an affine open chart of $M$ presented as a quotient of a polynomial ring. It feeds the verification of smoothness via such liftings, being used by [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed
    {R : Type} [CommRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R))
    (ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M) [IsOpenImmersion ι]
    (hι : ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))))
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m := by sorry
