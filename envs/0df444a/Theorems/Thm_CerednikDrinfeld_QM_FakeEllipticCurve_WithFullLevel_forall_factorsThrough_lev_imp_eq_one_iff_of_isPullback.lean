-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b61117cc-519b-5da4-a2e5-3dfca36a73f4
-- title:
--   Base change invariance of the level factorisation condition
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $u = (E,P)$ be a fake elliptic curve over $S$ with level structure $\Lambda$, $N$ together with a full level-$m$ structure, and let $u' = (E',P')$ be such a datum over $S'$, and assume `FakeEllipticCurve.WithFullLevel.IsPullback φ u u'`: there is a morphism $g : E'.A \to E.A$ making $(g, E'.f, E.f, \operatorname{Spec}\varphi)$ a cartesian square, such that post-composition with $g$ carries products for the relative group law of $E'$ to products for that of $E$, satisfies $E'.\mathrm{act}\,x \text{ followed by } g = g \text{ followed by } E.\mathrm{act}\,x$ for all $x \in \Lambda$, carries any point factoring through $E'.\mathrm{lev}$ to one whose composite with $g$ factors through $E.\mathrm{lev}$, and sends $P'$ to the base change of $P$ along $\varphi$. Let $k$ be an algebraically closed field, $sk' : S' \to k$ a ring homomorphism, $L_0$ a further $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ and $n$ a natural number. The conclusion is an equivalence of two statements: for every $x \in \Lambda$ whose underlying quaternion lies in $L_0$, if the point obtained from the level section at the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S'$ given by $sk'$, multiplied $n$ times by the group law and then pushed forward by $\mathrm{act}\,x$, factors through $E'.\mathrm{lev}$, then it equals the identity section over that geometric point; and the same assertion for $u$ over the geometric point of $\operatorname{Spec} S$ given by $sk' \circ \varphi$.
--
--   This is the compatibility of the condition "$x\cdot nP$ lies on the level subscheme only if it vanishes", imposed on geometric points of the base, with base change of fake elliptic curves with full level structure. It is used in the verification that the scheme representing the moduli problem is a fine moduli space, where the locus cut out by this condition must be shown to be defined independently of the chosen base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
    (k : Type u) [Field k] [IsAlgClosed k] (sk' : S' →+* k) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') n (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') n (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk')) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) n (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) n (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ))) := by sorry
