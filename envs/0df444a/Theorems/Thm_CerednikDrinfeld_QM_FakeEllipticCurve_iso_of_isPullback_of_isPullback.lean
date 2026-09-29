-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/71456230-1757-5a00-8356-92ebd93f2328
-- title:
--   Uniqueness up to isomorphism of pull-backs of fake elliptic curves
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number, let $S,S'$ be commutative rings and $\varphi\colon S\to S'$ a ring homomorphism. Let $E$ be a term of the structure `QM.FakeEllipticCurve Λ N S` and let $E',E''$ be terms of `QM.FakeEllipticCurve Λ N S'`; such a term consists of a scheme $A$ with a morphism $f\colon A\to\operatorname{Spec}S$, a commutative relative group law $L$ on the functor of points of $f$, the bundle of properties asserting $f$ smooth and proper with connected fibres and admitting a relative group law, fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms of $A$ over $\operatorname{Spec}S$ which is additive and multiplicative in $\Lambda$, is a homomorphism for $L$ on points and satisfies a trace condition on tangent spaces at geometric points, together with a level datum consisting of a scheme $C$ and a morphism `lev`$\colon C\to A$ and its further axioms. Assume `IsPullback φ E E'` and `IsPullback φ E E''`, that is: for $i\in\{',''\}$ there is $g\colon E^{i}.A\to E.A$ making the square with $E^{i}.f$, $E.f$ and $\operatorname{Spec}\varphi$ cartesian, such that composition with $g$ turns the multiplication of $T$-points over $t'\colon T\to\operatorname{Spec}S'$ into the multiplication of $T$-points over $t'$ followed by $\operatorname{Spec}\varphi$, such that $E^{i}.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $E.\mathrm{act}(x)$ for all $x\in\Lambda$, and such that every $T$-point factoring through $E^{i}.\mathrm{lev}$ has its composite with $g$ factoring through $E.\mathrm{lev}$. The conclusion is `Iso E' E''`: there is an isomorphism $e\colon E'.A\cong E''.A$ with $e$ followed by $E''.f$ equal to $E'.f$, compatible with the multiplication of $T$-points over any $t\colon T\to\operatorname{Spec}S'$, satisfying $E'.\mathrm{act}(x)$ followed by $e$ equals $e$ followed by $E''.\mathrm{act}(x)$ for all $x\in\Lambda$, and such that a $T$-point factors through $E'.\mathrm{lev}$ if and only if its composite with $e$ factors through $E''.\mathrm{lev}$.
--
--   This is the uniqueness half of the base-change construction for the moduli problem of fake elliptic curves with $\Lambda$-action and level-$N$ structure: the pull-back along $\varphi$, when it exists, is determined up to isomorphism of such data. It is used in the comparison of fibres of the moduli problem over varying bases, in particular in the statements producing a flat surjective extension carrying full level structure and in the construction of algebraic charts from period maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : QM.FakeEllipticCurve Λ N S) (E' E'' : QM.FakeEllipticCurve Λ N S')
    (h' : QM.FakeEllipticCurve.IsPullback φ E E') (h'' : QM.FakeEllipticCurve.IsPullback φ E E'') :
    QM.FakeEllipticCurve.Iso E' E'' := by sorry
