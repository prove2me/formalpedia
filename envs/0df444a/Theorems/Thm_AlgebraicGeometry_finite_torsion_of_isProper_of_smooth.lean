-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_torsion_of_isProper_of_smooth
-- name    : AlgebraicGeometry.finite_torsion_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/9490afa6-7f0f-5b13-ab09-e16a7478a786
-- title:
--   Finiteness of n-torsion on a smooth proper group scheme
-- statement:
--   Let $K$ be an algebraically closed field and let $J$ be a scheme equipped with a morphism $c \colon J \to \operatorname{Spec} K$ that is smooth and proper. Let $\mathrm{mul} \colon J \times_c J \to J$ be any morphism out of the pullback of $c$ along itself. Let $G$ be an additive commutative group together with a bijection $\mathrm{pts}$ from $G$ onto the set of sections of $c$, i.e. of morphisms $\sigma \colon \operatorname{Spec} K \to J$ with $\sigma$ followed by $c$ equal to the identity of $\operatorname{Spec} K$, and assume that $\mathrm{pts}$ is compatible with $\mathrm{mul}$ in the sense that for all $x, y \in G$ the section $\mathrm{pts}(x+y)$ is the morphism $\operatorname{Spec} K \to J \times_c J$ induced by the pair $(\mathrm{pts}\,x, \mathrm{pts}\,y)$ (the two composites with $c$ agreeing, both being the identity) followed by $\mathrm{mul}$. Let $n$ be a natural number whose image in $K$ is nonzero. Then the subtype $\{x \in G : n \cdot x = 0\}$ is finite. No associativity, unit or inverse compatibility for $\mathrm{mul}$ is assumed beyond the group structure carried by $G$ itself.
--
--   This is the finiteness half of the classical fact that multiplication by $n$ on an abelian variety over a field in which $n$ is invertible is an isogeny, so that the $n$-torsion of the group of geometric points is finite (of order $n^{2g}$). It is used in the analysis of the torsion of Néron models of Jacobians of modular curves, where it feeds the comparison of toric and finite points at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_torsion_of_isProper_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

theorem AlgebraicGeometry.finite_torsion_of_isProper_of_smooth
    (K : Type*) [Field K] [IsAlgClosed K]
    (J : AlgebraicGeometry.Scheme)
    (c : J ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hsm : AlgebraicGeometry.Smooth c)
    (hpr : AlgebraicGeometry.IsProper c)
    (mul : CategoryTheory.Limits.pullback c c ⟶ J)
    (G : Type*) [AddCommGroup G]
    (pts : G ≃ {σ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J // σ ≫ c = 𝟙 _})
    (hadd : ∀ x y : G, (pts (x + y)).1 =
      CategoryTheory.Limits.pullback.lift (pts x).1 (pts y).1
        ((pts x).2.trans (pts y).2.symm) ≫ mul)
    (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite {x : G // n • x = 0} := by sorry
