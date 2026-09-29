-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_isTwist_of_isTwist_of_sub_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/72bcdaee-9b4f-564c-8da2-827340647551
-- title:
--   Twists by labels congruent modulo mΛ are isomorphic
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Fix natural numbers $N,m$ and a commutative ring $S$. Let $u,u',u''$ be fake elliptic curves over $S$ with $\Lambda$-action and level datum indexed by $N$, each equipped with a full level-$m$ structure: a section $P$ of the structure morphism over $\mathrm{Spec}\,S$ which is killed by $m$ for the relative group law, whose $\Lambda$-translates exhaust the $m$-torsion at every geometric point, and whose annihilator in $\Lambda$ is exactly $m\Lambda$. Let $c,c' \in \Lambda$, and assume $u'$ is the twist of $u$ by $c$ and $u''$ the twist of $u$ by $c'$; that is, there is an isomorphism of the underlying schemes over $\mathrm{Spec}\,S$ compatible with the relative group laws on $T$-points, commuting with the $\Lambda$-actions, preserving the property of a point factoring through the level morphism `lev`, and carrying the $c$- (resp. $c'$-) translate of $u$'s level point to the level point of $u'$ (resp. $u''$). Assume finally that $c - c' = m\cdot y$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $y \in \Lambda$. Then $u'$ and $u''$ are isomorphic as fake elliptic curves with full level-$m$ structure: there is an isomorphism over $\mathrm{Spec}\,S$ compatible with the group laws, the $\Lambda$-actions and factorisation through `lev`, and matching the two level points on the nose.
--
--   The statement says that the twisting action of $\Lambda$ on full level-$m$ structures on fake elliptic curves factors through $\Lambda/m\Lambda$, so that a twist depends only on the label modulo $m\Lambda$. It is used in the fine-moduli part of the Čerednik–Drinfeld development, both for the equivariance of the identification of the moduli problem with a pullback under label-compatible data and for the description of quotients of points by the level-twisting action over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_isTwist_of_isTwist_of_sub_eq_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u u' u'' : FakeEllipticCurve.WithFullLevel Λ N m S) (c c' : ↥Λ)
    (h' : FakeEllipticCurve.WithFullLevel.IsTwist c u u') (h'' : FakeEllipticCurve.WithFullLevel.IsTwist c' u u'')
    (hcc' : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) - (c' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    FakeEllipticCurve.WithFullLevel.Iso u' u'' := by sorry
