-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/62a7c071-c317-5bed-896b-ec2a451a01d1
-- title:
--   Base change of a fake elliptic curve with full level structure
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and natural numbers $N,m$. Let $\varphi : S \to S'$ be a homomorphism of commutative rings (with $S,S'$ in `Type`), and let $u = (E,P)$ be an element of `FakeEllipticCurve.WithFullLevel Λ N m S`, that is, a fake elliptic curve $E$ over $S$ of level $N$ in the sense of the project's structure `FakeEllipticCurve` (a scheme $E.A$ proper and smooth over $\operatorname{Spec} S$ with connected two-dimensional fibres, a commutative relative group law on its functor of points, an action `act` of $\Lambda$ compatible with the group law and with multiplication and addition in $\Lambda$, the trace condition on the induced action on tangent spaces at geometric points, and level data `C`, `lev`), together with a full level-$m$ structure $P$: an $S$-point of $E.A$ killed by $m$ whose $\Lambda$-translates exhaust the $m$-torsion at every geometric point and whose annihilator in $\Lambda$ is $m\Lambda \cap \Lambda$. The conclusion asserts the existence of $u' = (E',P')$ over $S'$ of the same kind together with a morphism $g : E'.A \to E.A$ making the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ cartesian, such that $g$ carries products of $T$-points of $E'$ to products of their images, commutes with the $\Lambda$-action, carries points factoring through $E'.\mathrm{lev}$ to points factoring through $E.\mathrm{lev}$, and satisfies $P'$ followed by $g$ equals $\operatorname{Spec}\varphi$ followed by $P$; that is, `WithFullLevel.IsPullback φ u u'` holds.
--
--   This is the statement that the moduli problem of fake elliptic curves with $\Lambda$-action, level-$N$ data and full level-$m$ structure is covariantly functorial in the base ring: every object admits a base change along an arbitrary ring homomorphism. It is used throughout the construction of the associated moduli space, for instance in the uniqueness of morphisms compatible with pullback, in passing to directed colimits of base rings, and in the analysis over algebraically closed fields of positive characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by sorry
