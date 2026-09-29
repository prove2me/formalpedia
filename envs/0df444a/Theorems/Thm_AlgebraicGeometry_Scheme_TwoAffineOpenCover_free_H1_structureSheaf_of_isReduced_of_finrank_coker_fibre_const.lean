-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1503f5cb-7b8b-5f71-8b36-368fec9b1328
-- title:
--   Freeness and base change of two-chart Čech H¹
-- statement:
--   Let $R$ be a reduced Noetherian local commutative ring, $X$ a scheme, $\mathcal V$ a `TwoAffineOpenCover` of $X$ — that is, two opens $U_0,U_1$ of $X$ which are affine, have affine intersection and satisfy $U_0\sqcup U_1=\top$ — and $c\colon X\to\operatorname{Spec}R$ a morphism. Via $c$ the sections $\Gamma(X,U_0)$, $\Gamma(X,U_1)$, $\Gamma(X,U_0\cap U_1)$ become $R$-algebras with the two restrictions as $R$-algebra maps, giving the two-chart cover `𝒱.cover c`; `𝒱.structureSheafSections c` is the associated system of sections `(𝒱.cover c).structureSheaf`, whose Čech differential is $(-r_0)\sqcup r_1$ on $M_0\times M_1$ with values in $M_{01}$, and whose $H^1$ is the quotient of $M_{01}$ by the range of that differential. Assume $H^1$ is a finite $R$-module, and that for some $n\in\mathbb N$ and every prime $\mathfrak p$ of $R$ the $\kappa(\mathfrak p)$-dimension of $(\kappa(\mathfrak p)\otimes_R(\mathcal V.\mathrm{cover}\,c).A_{01})$ modulo the range of the base-changed Čech differential equals $n$. Then $H^1$ is a free $R$-module of rank $n$, and for every commutative $R$-algebra $A$ (in the same universe) there are an $A$-algebra isomorphism $e_{01}$ from $A\otimes_R\Gamma(X,U_0\cap U_1)$ onto the $A_{01}$ of the cover `𝒱.pullback c A` taken with structure morphism $\mathrm{pr}_2$, and an $A$-linear isomorphism $e$ from $A\otimes_R H^1$ onto the corresponding $H^1$ of the pulled-back sections, such that $e_{01}(1\otimes s)$ is the image of $s$ under the component of $\mathrm{pr}_1$ at $U_0\cap U_1$, and $e(a\otimes[y])=[e_{01}(a\otimes y)]$ for all $a\in A$ and $y\in\Gamma(X,U_0\cap U_1)$.
--
--   This is cohomology and base change in degree $1$ over a reduced base, in the two-affine-chart Čech formulation: constancy of the fibre dimension of $\check H^1$ forces freeness and compatibility with arbitrary base change. It is used in the comparison of the rank of $H^0$ of the module of Kähler differentials with that of $\check H^1(\mathcal O_X)$ for a relative curve, for smooth morphisms of relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H1) {n : ℕ}
    (hH1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[R] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.structureSheafSections c).H1 ∧
      Module.finrank R (𝒱.structureSheafSections c).H1 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        ∃ (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
            ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
          (e : A ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections
              (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
          (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
              = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
          ∀ (a : A) (y : (𝒱.cover c).A01),
            e (a ⊗ₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 (a ⊗ₜ[R] y)) := by sorry
