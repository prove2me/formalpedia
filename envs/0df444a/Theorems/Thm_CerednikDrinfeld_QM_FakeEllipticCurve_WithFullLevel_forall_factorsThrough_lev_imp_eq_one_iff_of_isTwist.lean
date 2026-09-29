-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/285dcf16-742b-5f39-8c95-3432d6ec50ab
-- title:
--   Twist-invariance of the lev-factorisation condition
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, and is finitely generated), natural numbers $N,m$ and a commutative ring $S$. Let $u=(E,P)$ and $u'=(E',P')$ be fake elliptic curves over $S$ for $(\Lambda,N)$ equipped with full level-$m$ structures, and let $c\in\Lambda$ be such that $u'$ is a twist of $u$ by $c$: there is an isomorphism $e:E.A\cong E'.A$ over $S$ which is a homomorphism for the relative group laws, intertwines the $\Lambda$-actions ($E.\mathrm{act}\,x$ followed by $e$ equals $e$ followed by $E'.\mathrm{act}\,x$), matches the conditions of factoring through the maps $E.\mathrm{lev}$ and $E'.\mathrm{lev}$, and carries the image of $P$ under $E.\mathrm{act}\,c$ to $P'$. Let $\ell$ be a natural number dividing $m$, and let $L_0$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ contained in $\Lambda$ with $L_0c\subseteq L_0$ and such that every $y\in\Lambda\cap L_0$ can be written $y=xc+\ell z$ with $x,z\in\Lambda$ and $x\in L_0$. Let $k$ be an algebraically closed field and $sk:S\to k$ a ring homomorphism, giving the geometric point $\operatorname{Spec}k\to\operatorname{Spec}S$. Then the following two conditions are equivalent: for every $x\in\Lambda$ lying in $L_0$, if the point obtained from the base change of $P'$ to $\operatorname{Spec}k$ by taking its $(m/\ell)$-fold multiple in the relative group law and then pushing forward along $E'.\mathrm{act}\,x$ factors through $E'.\mathrm{lev}$ (that is, its underlying morphism is $E'.\mathrm{lev}$ precomposed with some morphism $\operatorname{Spec}k\to E'.C$), then that point is the identity section; and the same condition with $u'$ replaced by $u$.
--
--   This is the invariance, under twisting a full level structure by an element $c$ of the order, of the condition that no nonzero $L_0$-multiple of the $\ell$-torsion part of the level structure meets the image of the level-$N$ map $\mathrm{lev}$. It is used in the verification that the quaternionic moduli problem with full level structure is a fine moduli problem, in [`CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type u} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (c : ↥Λ) (h : FakeEllipticCurve.WithFullLevel.IsTwist c u u')
    (ℓ : ℕ) (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ)
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L₀)
    (hsurj : ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ →
      ∃ x z : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ (y : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (z : ℍ[ℚ, a, b]))
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk)) = u'.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) := by sorry
