-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/23454c3b-0d79-5efc-a031-45f4266d6bbd
-- title:
--   Isomorphism invariance of the lev-vanishing condition at a geometric point
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m$, and a commutative ring $S$. Let $u=(E,P)$ and $u'=(E',P')$ be two elements of `FakeEllipticCurve.WithFullLevel Λ N m S`, i.e. pairs consisting of a `FakeEllipticCurve Λ N S` together with a `FullLevel m` structure on it, and let $h$ witness `WithFullLevel.Iso u u'`: an isomorphism $e$ of the underlying schemes with $e$ followed by $u'.1.f$ equal to $u.1.f$, such that $P\mapsto e\circ P$ on $T$-points over $S$ is multiplicative for the two relative group laws, commutes with the action of every $x\in\Lambda$, satisfies `FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)` for all points, and carries $u.2.P$ to $u'.2.P$. Let $k$ be an algebraically closed field, $sk : S\to k$ a ring homomorphism, with associated geometric point $\mathrm{Spec}\,k\to\mathrm{Spec}\,S$, let $L_0$ be a further $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, and let $n$ be a natural number. The assertion is the equivalence of the following two statements: for every $x\in\Lambda$ whose image in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $L_0$, if the point obtained by applying the action of $x$ to the $n$-th group-law multiple of the section $P$ at the geometric point factors through $\mathrm{lev}$, then that point equals the identity section at the geometric point; and the same statement for $u'$, $P'$ and $u'.1.\mathrm{lev}$.
--
--   This is the invariance, under isomorphism of fake elliptic curves with full level-$m$ structure, of the condition cutting out those $x \in L_0 \cap \Lambda$ for which $x\cdot nP$ is both in the image of $\mathrm{lev}$ and trivial at a given geometric point. It is used in the fine-moduli analysis, in [`CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp), to see that the condition depends only on the isomorphism class of the pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type u} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : FakeEllipticCurve.WithFullLevel.Iso u u')
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u'.2.P k sk))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u'.2.P k sk)) = u'.1.L.one (geomPoint k sk)) := by sorry
