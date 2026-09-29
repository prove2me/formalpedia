-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/100a76b2-d1d5-5d9c-9be8-be7c664ad56b
-- title:
--   Atkin–Lehner quotients are preserved under base change
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a level $N\in\mathbb{N}$, a homomorphism $\varphi : S \to S'$ of commutative rings and $r\in\mathbb{N}$. Let $E,E_1$ be objects of `QM.FakeEllipticCurve` $\Lambda$ $N$ $S$ and $E',E_1'$ objects over $S'$; each such object consists of a scheme $A$ proper and smooth over $\operatorname{Spec} S$ with connected fibres of topological Krull dimension $2$, a commutative relative group law on its $T$-points, an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative in the $\Lambda$-variable and whose trace on the tangent space at a geometric point is the reduced trace, together with level data given by a scheme $C$ and a morphism `lev`. Assume `IsPullback` $\varphi$ holds for $(E,E')$ and for $(E_1,E_1')$: there is $g : E'.A \to E.A$ making $E'.f$, $E.f$, $\operatorname{Spec}\varphi$ a cartesian square, compatible with the group laws on points, commuting with the $\Lambda$-actions, and carrying points that factor through $E'.\mathrm{lev}$ to points whose composite with $g$ factors through $E.\mathrm{lev}$. Assume further `IsAtkinLehnerQuotient` $r$ $E$ $E_1$, i.e. there are morphisms $\phi : E.A \to E_1.A$ and $\psi : E_1.A \to E.A$ over $\operatorname{Spec} S$, both additive on $T$-points and commuting with the $\Lambda$-actions, such that (when $r\in\Lambda$) $\phi$ followed by $\psi$ is the action of $r$ on $E$ and $\psi$ followed by $\phi$ the action of $r$ on $E_1$, such that a point $P$ is killed by $\phi$ precisely when $m\cdot P=0$ for every $m\in\Lambda$ with $m\,\overline{m}=rn$ for some $n\in\mathbb{Z}$, and such that $\phi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E_1.\mathrm{lev}$. The conclusion is that `IsAtkinLehnerQuotient` $r$ $E'$ $E_1'$ holds over $S'$.
--
--   This is the base-change compatibility of the moduli-theoretic Atkin–Lehner correspondence at $r$ for fake elliptic curves with quaternionic multiplication: the pair of isogenies realising the quotient descends along any ring homomorphism once both curves are pulled back. It is used in the converse direction (recognising a pull-back from two Atkin–Lehner quotients), in the comparison of lifted points with the base-changed Atkin–Lehner maps, and in the verification of the tower relations for the moduli witness in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (E E₁ : QM.FakeEllipticCurve Λ N S) (E' E₁' : QM.FakeEllipticCurve Λ N S')
    (hE : QM.FakeEllipticCurve.IsPullback φ E E') (hE₁ : QM.FakeEllipticCurve.IsPullback φ E₁ E₁')
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E₁) :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E' E₁' := by sorry
