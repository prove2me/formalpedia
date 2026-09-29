-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_eq_one_of_level_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8665a5d4-6ac3-5a49-aefa-e5e99615fbf3
-- title:
--   Level-one structure meets exactly the unit section
-- statement:
--   Fix rational numbers $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a commutative ring $S$, and a fake elliptic curve $E$ of level $N = 1$ over $S$ with $\Lambda$-action, i.e. an object of the structure `FakeEllipticCurve` consisting of a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a relative group law $E.L$ on the functor of points of $E.f$ which is commutative, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law exists), two-dimensional fibres, an action of $\Lambda$ by $S$-morphisms compatible with the group law and with traces, and level data consisting of a scheme $E.C$, a morphism $E.\mathrm{lev}$ into $E.A$ and the accompanying axioms $E.\mathrm{lev\_torsion}$ and $E.\mathrm{lev\_one}$. Let $T$ be a scheme, $t : T \to \operatorname{Spec} S$ a morphism, and $P$ a point of $E.A$ over $t$, that is, a morphism $T \to E.A$ whose composite with $E.f$ is $t$. The assertion is that $P$ factors through the level structure, i.e. there is $P_0 : T \to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$, if and only if $P$ is the unit point $E.L.\mathrm{one}\ t$.
--
--   This identifies, for level $N = 1$, the points cut out by the level structure with the unit section, so that a level-one structure imposes no condition on points. It is used in the construction of the fine moduli problem for fake elliptic curves of level one and in the local power-series (Čerednik–Drinfeld uniformisation) statements attached to it, where level-one points must be recognised as the pulled-back ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_eq_one_of_level_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough E.lev P ↔ P = E.L.one t := by sorry
