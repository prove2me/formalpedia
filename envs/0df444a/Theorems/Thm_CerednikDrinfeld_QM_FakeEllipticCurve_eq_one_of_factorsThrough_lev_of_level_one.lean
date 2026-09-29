-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_factorsThrough_lev_of_level_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_factorsThrough_lev_of_level_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3b6ef962-f04b-5b83-8629-dbb34425dce1
-- title:
--   Points through the level subscheme are the unit when N=1
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $S$ be a commutative ring, and let $E$ be a fake elliptic curve of level $N = 1$ over $S$ with $\Lambda$-action, i.e. a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on $T$-points over $\operatorname{Spec} S$, smoothness, properness and connectedness of fibres together with existence of a group law (the bundle `AbelianSchemePropertyBundle`), all fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms of $E.A$ over $S$ which is additive and multiplicative in $\Lambda$, compatible with the group law, sends $1$ to the identity and satisfies the trace condition on tangent spaces, and a level datum consisting of a scheme $E.C$ with a morphism $E.\mathrm{lev} : E.C \to E.A$ and its axioms. Let $T$ be a scheme, $t : T \to \operatorname{Spec} S$, and let $P$ be a $T$-point of $E.A$ over $t$, that is, a morphism $T \to E.A$ whose composite with $E.f$ is $t$. If `FactorsThrough E.lev P` holds, i.e. there is $P_0 : T \to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$, then $P$ is the unit $T$-point $E.L.\mathrm{one}\, t$.
--
--   This records that for a fake elliptic curve whose level is $1$ the level subscheme carries no points beyond the unit section, so a level-one structure imposes no extra condition on $T$-points. It is used in the construction and comparison of fake elliptic curves over towers and in the pullback/pushout arguments for level-one data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_factorsThrough_lev_of_level_one.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_factorsThrough_lev_of_level_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (hP : FactorsThrough E.lev P) :
    P = E.L.one t := by sorry
