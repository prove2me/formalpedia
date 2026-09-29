-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/d08eb258-4438-5903-b442-c751f2f9afca
-- title:
--   Split sections of C_{R'} factoring through a block
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism. Let $R'$ be a nontrivial commutative $R$-algebra, $B$ a commutative $R$-algebra, $d$ a natural number, and $\varphi \colon R' \otimes_R B \to (\mathrm{Fin}\,d \to R')$ an isomorphism of $R'$-algebras. Let $z \colon \operatorname{Spec} B \to C$ be a monomorphism of schemes lying over $\operatorname{Spec} R$, in the sense that $z$ followed by $c$ equals $\operatorname{Spec}$ of the structure map $R \to B$. The assertion is that there is a family $\sigma$ indexed by $\mathrm{Fin}\,d$ of sections of the base change $\mathrm{pr}_2 \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$ — each $\sigma\,m$ being a morphism $\operatorname{Spec} R' \to C \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ together with a proof that it followed by the second projection is the identity of $\operatorname{Spec} R'$ — such that $\sigma$ is injective, and such that for every $m$ there exists $y \colon \operatorname{Spec} R' \to \operatorname{Spec} B$ with $\sigma\,m$ followed by the first projection $C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to C$ equal to $y$ followed by $z$. Thus the $d$ sections are pairwise distinct and each factors through the block $z$.
--
--   If $R'$ splits the $R$-algebra $B$ into $d$ copies of $R'$, then the $R$-points of $C$ cut out by the monomorphism $\operatorname{Spec} B \to C$ produce $d$ distinct $R'$-sections of $C_{R'}$, each visibly factoring through $\operatorname{Spec} B$. The factorisation clause is what is needed downstream, in the construction of two-sided chart data and of charts for the relative Picard scheme, where one must know that a whole orbit of sections lands inside a single prescribed block.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve TensorProduct NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Nontrivial R']
    (B : Type u) [CommRing B] [Algebra R B] (d : ℕ) (φ : R' ⊗[R] B ≃ₐ[R'] (Fin d → R'))
    (z : Spec (CommRingCat.of B) ⟶ C) [Mono z] (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'),
      Function.Injective σ ∧
      ∀ m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B),
        (σ m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z := by sorry
