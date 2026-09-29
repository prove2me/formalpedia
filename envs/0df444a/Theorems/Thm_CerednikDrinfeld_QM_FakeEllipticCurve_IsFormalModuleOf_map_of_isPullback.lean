-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_map_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.map_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/8d78ac45-17b7-5408-8bfe-24d36fca1cb6
-- title:
--   Base change of the formal 𝒪_D-module of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a prime $q$, and let $\mathrm{coord} : \Lambda \to \mathrm{Zp2}\,q \times \mathrm{Zp2}\,q$ be any map to pairs of Witt vectors over $\mathbb{F}_{q^2}$. Let $\varphi : B \to B'$ be a homomorphism of commutative rings, let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $B$ and $E'$ one over $B'$, and assume `FakeEllipticCurve.IsPullback φ E E'`: there is a morphism $g : E'.A \to E.A$ making the square formed by $E'.f$, $E.f$ and $\mathrm{Spec}\,\varphi$ cartesian, such that $g$ carries products for the relative group law $E'.L$ to products for $E.L$, satisfies $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for every $x \in \Lambda$, and sends points factoring through $E'.\mathrm{lev}$ to points factoring through $E.\mathrm{lev}$. Let $X$ be a formal $\mathcal{O}_D$-module over $B$ of dimension $2$ at $q$ (a commutative formal group law $X.F$ in two variables, an action of $\mathrm{Zp2}\,q$ by series, and a uniformiser series $X.\varpi$ with $X.\varpi \circ X.\varpi = X.\mathrm{act}\,q$ and $X.\varpi \circ X.\mathrm{act}\,\alpha = X.\mathrm{act}(\mathrm{Frob}\,\alpha) \circ X.\varpi$). Assume $E$ has $X$ as formal $\mathcal{O}_D$-module via $\mathrm{coord}$, i.e. there are formal coordinates $\theta$ of $E.f$ in two variables such that `E.L.IsFormalCoordinates X.F θ` holds and, for every $B$-algebra $B''$, every ideal $J$ with $J^{n+1} = \bot$, every $m \in \Lambda$ and every tuple $s : \mathrm{Fin}\,2 \to J$, the value of $\theta$ at the nilpotent evaluation of $\mathrm{addVia}\,X.F\,(X.\mathrm{act}\,(\mathrm{coord}\,m)_1)\,((X.\mathrm{act}\,(\mathrm{coord}\,m)_2) \circ X.\varpi)$ at $s$ is the pushforward of $\theta(s)$ along $E.\mathrm{act}\,m$. The conclusion is that $E'$ then has as formal $\mathcal{O}_D$-module via the same $\mathrm{coord}$ the coefficientwise base change $X.\mathrm{map}\,\varphi$, obtained by applying $\varphi$ to the coefficients of $X.F$, of all action series and of $X.\varpi$.
--
--   This is the compatibility of the formal $\mathcal{O}_D$-module attached to a fake elliptic curve with base change along a ring homomorphism, in the form needed to move the Drinfeld-module structure along a cartesian square of fake elliptic curves. It is used when passing from a fake elliptic curve over a ring to its specialisations and to the complete local rings of the moduli problem, in the construction of fake elliptic curves with prescribed formal module and in the pro-representability of stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_map_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.map_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (hE : FakeEllipticCurve.IsPullback φ E E')
    (X : FormalODModule q B) (hX : E.IsFormalModuleOf coord X) :
    E'.IsFormalModuleOf coord (X.map φ) := by sorry
