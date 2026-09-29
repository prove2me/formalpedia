-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/cf41f857-a884-5afb-a951-41c81808be69
-- title:
--   Two-chart Čech sections data commute with base change
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal{V}$ a two-affine open cover datum for $X$, that is, opens $U_0,U_1$ of $X$ with $U_0$, $U_1$ and $U_0\cap U_1$ affine and $U_0\sqcup U_1=\top$; let $c\colon X\to\operatorname{Spec} R$ be a morphism, $M$ a sheaf of modules on $X$, and suppose that every point of $X$ has an open neighbourhood $V$ such that the pullback of $M$ along the inclusion $V\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $V$. Let $A$ be a commutative $R$-algebra. Write $q=\mathrm{pr}_1$ and $r=\mathrm{pr}_2$ for the two projections of the pullback of $c$ along $\operatorname{Spec}(A)\to\operatorname{Spec}(R)$, and form the two-affine cover of that pullback with opens $q^{-1}U_0, q^{-1}U_1$ and its sections datum for $q^{*}M$ over $r$. Then there are $A$-linear isomorphisms $e_0\colon A\otimes_R\Gamma(M,U_0)\to\Gamma(q^{*}M,q^{-1}U_0)$, $e_1\colon A\otimes_R\Gamma(M,U_1)\to\Gamma(q^{*}M,q^{-1}U_1)$ and $e_{01}\colon A\otimes_R\Gamma(M,U_0\cap U_1)\to\Gamma(q^{*}M,q^{-1}(U_0\cap U_1))$ (the source $R$-module structures coming from $c$ via $R\to\Gamma(X,U)$) such that $e_{01}$ intertwines the base change along $A$ of each restriction map $r_0,r_1$ of the sections datum of $M$ with the corresponding restriction map of the sections datum of $q^{*}M$, and such that each $e$ sends $1\otimes m$ to the value at the relevant open of the unit of the pullback–pushforward adjunction for $q$ evaluated at $M$, applied to $m$.
--
--   This is the base-change compatibility of the two-chart Čech datum of a Zariski-locally trivial sheaf of modules: the datum of the pulled-back module on the pulled-back cover is $A\otimes_R$ of the original datum, with the comparison maps normalised by pullback of sections. It feeds the computations of $\check H^0$ and $\check H^1$ under base change used in the relative Picard functor arguments, and is cited in the statements on fibrewise ranks of $H^0$ and $H^1$, on invertible modules over nilpotent thickenings, and on surjectivity of the adjunction unit when $H^1$ vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : A ⊗[R] (𝒱.sectionsOf c M).M0 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0)
      (e1 : A ⊗[R] (𝒱.sectionsOf c M).M1 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1)
      (e01 : A ⊗[R] (𝒱.sectionsOf c M).M01 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M01),
      (∀ x, e01 (((𝒱.sectionsOf c M).r0.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r0
            (e0 x)) ∧
      (∀ x, e01 (((𝒱.sectionsOf c M).r1.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r1
            (e1 x)) ∧
      (∀ m : (𝒱.sectionsOf c M).M0, e0 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app 𝒱.U0).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M1, e1 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app 𝒱.U1).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M01, e01 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app (𝒱.U0 ⊓ 𝒱.U1)).hom m) := by sorry
