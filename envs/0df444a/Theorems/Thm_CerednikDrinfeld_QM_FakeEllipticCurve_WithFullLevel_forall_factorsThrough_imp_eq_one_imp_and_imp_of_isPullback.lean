-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/bfde2b11-2bf3-5e73-94fd-5d73a90e85fb
-- title:
--   Transversality clause descends, and ascends when N is invertible
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m,\ell$, a further $\mathbb{Z}$-submodule $L_0$ of $\mathbb{H}[\mathbb{Q},a,b]$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $u=(E,P)$ and $u'=(E',P')$ be pairs consisting of a fake elliptic curve with level-$N$ data over $S$, resp. over $S'$, together with a full level-$m$ structure, and assume `FakeEllipticCurve.WithFullLevel.IsPullback` for $\varphi$, $u$, $u'$: there is a morphism $g : E'.A \to E.A$ such that the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ is cartesian, $g$ carries products for the group law $E'.L$ to products for $E.L$, satisfies $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$, sends any point factoring through $E'.\mathrm{lev}$ to one factoring through $E.\mathrm{lev}$ after composing with $g$, and satisfies $P'$ followed by $g$ equals $\operatorname{Spec}\varphi$ followed by $P$. For an algebraically closed field $k$ and a ring homomorphism $s : S'' \to k$ (with $S''=S$ or $S'$), write $T(v,s)$ for the clause: for every $x \in \Lambda$ whose underlying quaternion lies in $L_0$, if the point obtained by applying $v.1.\mathrm{act}\,x$ to the $\lfloor m/\ell\rfloor$-fold multiple (natural division) of the geometric fibre $v.2.P$ at $\operatorname{Spec} s$ factors through $v.1.\mathrm{lev}$, then that point is the identity section of $v.1.L$ at $\operatorname{Spec} s$. The conclusion is the conjunction: for every algebraically closed $k$ and every $s' : S' \to k$, $T(u,s'\circ\varphi)$ implies $T(u',s')$; and, for every such $k$ and $s'$ with the image of $N$ in $k$ nonzero, $T(u',s')$ implies $T(u,s'\circ\varphi)$.
--
--   The clause $T$ is the transversality condition under which an extra level structure is cut out of a full level-$m$ structure by the multiplier module $L_0$; this statement says that it passes from a fake elliptic curve to any base change, and passes back when $N$ is invertible in the residue field. It is used in the construction of local algebraic families of fake elliptic curves carrying an extra level at a prime, for the fine moduli description in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k),
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ))) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk'))) ∧

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k), (N : k) ≠ 0 →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk')) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ)))) := by sorry
