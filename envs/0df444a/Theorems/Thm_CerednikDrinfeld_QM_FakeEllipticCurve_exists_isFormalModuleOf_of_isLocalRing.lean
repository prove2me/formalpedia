-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleOf_of_isLocalRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleOf_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/bd4cdfa8-f93a-5226-bfad-edff3db763e8
-- title:
--   Global formal mathcal O_D-module over a local base
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and a prime $q$. Let $\mathrm{coord}:\Lambda\to \mathbb Z_{q^2}\times\mathbb Z_{q^2}$, where $\mathbb Z_{q^2}$ denotes `Zp2 q`, the Witt vectors of the field with $q^2$ elements, and assume `IsOrderCoord`: $\mathrm{coord}$ is additive, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is injective, satisfies the twisted multiplication rule $\mathrm{coord}(mm')=(\alpha_m\alpha_{m'}+q\,\beta_m\varphi(\beta_{m'}),\ \alpha_m\beta_{m'}+\beta_m\varphi(\alpha_{m'}))$ with $\varphi$ the Witt-vector Frobenius, has $q$-adically dense image in each truncation, and satisfies $\alpha_m+\varphi(\alpha_m)=n$ whenever $m+\bar m=n\in\mathbb Z$. Let $B$ be a commutative local ring in which the image of $q$ is nilpotent, and let $E$ be a fake elliptic curve over $B$ of level $N$ with $\Lambda$-action, i.e. a scheme $E.A\to\operatorname{Spec}B$ with commutative relative group law $E.L$, abelian-scheme property bundle, all fibres of dimension $2$, an action $m\mapsto E.\mathrm{act}\,m$ of $\Lambda$ by group-law endomorphisms over the base compatible with $1$, products, sums and traces, together with the level data. The conclusion asserts the existence of a formal $\mathcal O_D$-module $X$ over $B$ — a commutative two-variable formal group law $X.F$ with an action $X.\mathrm{act}$ of $\mathbb Z_{q^2}$ by endomorphisms of $X.F$ and a uniformiser series $X.\varpi$ satisfying $X.\varpi\circ X.\varpi=X.\mathrm{act}(q)$ and $X.\varpi\circ X.\mathrm{act}(\alpha)=X.\mathrm{act}(\varphi\alpha)\circ X.\varpi$ — together with formal coordinates $\theta$ of dimension $2$ along $E.f$ which are formal coordinates for $X.F$ relative to $E.L$ and in which, for all $B$-algebras $B'$, all ideals $J$ with $J^{n+1}=0$, all $m\in\Lambda$ and all tuples $s$ with entries in $J$, the point $\theta$ of the nilpotent evaluation of $X.\mathrm{act}(\alpha_m)+_{X.F}X.\mathrm{act}(\beta_m)\circ X.\varpi$ at $s$ agrees with the image of $\theta(s)$ under $E.\mathrm{act}\,m$.
--
--   This is the statement that the formal $\mathcal O_D$-module attached to a fake elliptic curve in equal characteristic-$q$-nilpotent situations, which in general exists only Zariski-locally on the base, exists over the whole base when the base is local; it is the form of Drinfeld's formal-module description used in the Čerednik–Drinfeld uniformisation. It is invoked by the rigidification statements over Artinian and local rings and by the comparison of formal module structures in the ramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleOf_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleOf_of_isLocalRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsLocalRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B) :
    ∃ X : FormalODModule q B, E.IsFormalModuleOf coord X := by sorry
