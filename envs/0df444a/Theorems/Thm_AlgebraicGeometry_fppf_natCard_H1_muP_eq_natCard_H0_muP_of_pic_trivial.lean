-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial
-- name    : AlgebraicGeometry.fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/65cc698b-d575-5db5-83c2-ab38055062b2
-- title:
--   #H¹_{fppf}(μₚ)=#H⁰_{fppf}(μₚ) when H¹(G_m) is trivial
-- statement:
--   Fix a natural number $p$ with $p \neq 0$. Work on the big fppf site of schemes in the bottom universe, with abelian sheaves valued in additive commutative groups one universe up; for such a sheaf $F$, [`FppfCohomologyLES.FppfH F n`](def/AlgebraicGeometry_FppfCohomologyLES.html#L175) is its $n$-th sheaf cohomology `F.H n`. Here [`FppfKummerSES.GmAbelianSheafLifted`](def/AlgebraicGeometry_FppfKummerProp17.html#L387) is the universe lift (along `AddCommGrpCat.uliftFunctor`, applied to sheaves by `sheafCompose`) of the fppf sheaf `GmAbelianSheaf` represented by $\mathbb{G}_m$, i.e. the units sheaf regarded additively via `commGroupAddCommGroupEquivalence`; and [`FppfKummerSES.muPAbelianSheafLifted p`](def/AlgebraicGeometry_FppfKummerProp17.html#L608) is by definition the kernel of the endomorphism `gmPowSelf p` of that lifted sheaf, the lift of the $p$-th power map `gmPowAb p` on $\mathbb{G}_m$ — that is, the sheaf $\mu_p$. The hypothesis is that the first cohomology of the lifted $\mathbb{G}_m$ sheaf has `Nat.card` equal to $1$, i.e. it is a one-element type. The conclusion is an equality of natural cardinalities: `Nat.card` of $H^1$ of $\mu_p$ equals `Nat.card` of $H^0$ of $\mu_p$ (with the convention that `Nat.card` of an infinite type is $0$).
--
--   Since $\operatorname{Spec}\mathbb{Z}$ is terminal among schemes, cohomology on the big fppf site computes fppf cohomology over $\operatorname{Spec}\mathbb{Z}$, and the hypothesis expresses the vanishing of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mathbb{G}_m)$, i.e. triviality of the Picard group; the conclusion is the resulting collapse of the Kummer long exact sequence. It is used in the computation of fppf cohomology groups attached to modular curves, via [`ModularCurve.exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial.lean

import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Abelian Limits AlgebraicGeometry
open FppfCohomologyLES FppfKummerSES FppfRepresentableGroupSchemeSheaf FppfBigSiteH0Gm

theorem AlgebraicGeometry.fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial
    (p : ℕ) (hp : p ≠ 0)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) =
      Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 0) := by sorry
