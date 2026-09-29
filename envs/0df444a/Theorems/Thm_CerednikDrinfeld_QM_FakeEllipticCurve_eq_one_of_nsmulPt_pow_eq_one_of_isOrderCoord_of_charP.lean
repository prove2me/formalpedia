-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3accceab-45e8-5369-a945-f4ede2dcc5e9
-- title:
--   Fake elliptic curves have no q-power torsion in characteristic q
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$. Let $\mathrm{coord}\colon \Lambda \to \mathrm{Zp2}\,q \times \mathrm{Zp2}\,q$, where $\mathrm{Zp2}\,q$ is the ring of Witt vectors over $\mathbb{F}_{q^2}$, satisfy `IsOrderCoord`: it is additive, sends the element $1$ of $\Lambda$ to $(1,0)$, is injective, carries a product $m m'$ lying in $\Lambda$ to $((\mathrm{coord}\,m)_1(\mathrm{coord}\,m')_1 + q\,(\mathrm{coord}\,m)_2\,\varphi((\mathrm{coord}\,m')_2),\ (\mathrm{coord}\,m)_1(\mathrm{coord}\,m')_2 + (\mathrm{coord}\,m)_2\,\varphi((\mathrm{coord}\,m')_1))$ with $\varphi$ the Witt vector Frobenius, has image dense modulo every power of $q$ in both coordinates, and satisfies $(\mathrm{coord}\,m)_1 + \varphi((\mathrm{coord}\,m)_1) = n$ whenever $m + \bar m = n$ for an integer $n$. Assume $1 \in \Lambda$. Let $k$ be an algebraically closed field of characteristic $q$ and let $E$ be a fake elliptic curve over $k$ of level $N$ with $\Lambda$-action, that is, a scheme $A$ with a structure morphism $f\colon A \to \operatorname{Spec} k$ that is smooth, proper and has connected fibres, a commutative relative group law $L$ on $f$, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $A$ over $\operatorname{Spec} k$ that is additive in the acting element, anti-multiplicative on products, trivial on $1$, compatible with the group law, and whose induced endomorphism of any finite-dimensional space of tangent vectors has trace equal to the reduced trace of the acting element, together with the remaining level-$N$ data. Then for every natural number $m$ and every section $P$ of $f$ over the identity of $\operatorname{Spec} k$ (a morphism $\operatorname{Spec} k \to A$ composing with $f$ to the identity) with $q^m \cdot P$, formed by iterating $L$, equal to the unit section, one has that $P$ is the unit section. No hypothesis relates $q$ to the level $N$.
--
--   This is the statement that a fake elliptic curve at a prime $q$ ramified in the quaternion algebra (ramification being encoded by the twisted multiplication rule in `IsOrderCoord`, which presents $\Lambda \otimes \mathbb{Z}_q$ as the maximal order $\mathbb{Z}_{q^2} \oplus \mathbb{Z}_{q^2}\Pi$ of the quaternion division algebra over $\mathbb{Q}_q$) has no non-trivial geometric $q$-power torsion, i.e. that the abelian surface has $q$-rank zero. It is the input to the corresponding statement over an arbitrary field, [`CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem), from which the infinitesimality of the $q$-power torsion subschemes is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_isOrderCoord_of_charP
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
    (E : FakeEllipticCurve Λ N k) (m : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) (q ^ m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by sorry
