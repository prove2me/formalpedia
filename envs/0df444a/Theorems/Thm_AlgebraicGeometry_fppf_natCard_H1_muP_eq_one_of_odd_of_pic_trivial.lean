-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
-- name    : AlgebraicGeometry.fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/6a13e66c-f26f-5268-80cb-28a7cc7c54c0
-- title:
--   Vanishing of H¹_{fppf}(μₚ) for odd primes
-- statement:
--   Let $p$ be a natural number which is prime and odd. Work on the big fppf site `Scheme.fppfTopology` of schemes in the lowest universe, whose terminal object is $\operatorname{Spec}\mathbb{Z}$, and with abelian sheaves valued in additive commutative groups one universe higher. Here `GmAbelianSheafLifted` is the multiplicative group sheaf: the fppf sheaf $\mathbb{G}_m$, transported from commutative groups to additive commutative groups and then composed with the universe-lifting functor `AddCommGrpCat.uliftFunctor`; `muPAbelianSheafLifted p` is the kernel, in the abelian category of such sheaves, of the endomorphism `gmPowSelf p` obtained by lifting the $p$-th power map `gmPowAb p` of $\mathbb{G}_m$, i.e. the sheaf $\mu_p$ of $p$-th roots of unity; and `FppfH F n` is the $n$-th cohomology `F.H n` of an abelian sheaf $F$ on this site. The hypothesis is that the cohomology group $H^1$ of `GmAbelianSheafLifted` has cardinality $1$, `Nat.card` of its underlying type being $1$. The conclusion is that $H^1$ of `muPAbelianSheafLifted p` likewise has cardinality $1$, so that this group is trivial.
--
--   This is the computation $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mu_p)=\mathbb{Z}^\times/(\mathbb{Z}^\times)^p$ of Mazur's analysis of the Eisenstein ideal, in the form in which the quotient is trivial for odd $p$; the oddness hypothesis is essential, since for $p=2$ the group has order $2$. It is used in the finiteness statement for fppf $H^1$ over $\operatorname{Spec}\mathbb{Z}$ and in the estimate of cokernel and $H^1$ contributions for the primary torsion of the Néron model of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial.lean

import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Abelian Limits AlgebraicGeometry
open FppfCohomologyLES FppfKummerSES FppfRepresentableGroupSchemeSheaf FppfBigSiteH0Gm

theorem AlgebraicGeometry.fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) = 1 := by sorry
