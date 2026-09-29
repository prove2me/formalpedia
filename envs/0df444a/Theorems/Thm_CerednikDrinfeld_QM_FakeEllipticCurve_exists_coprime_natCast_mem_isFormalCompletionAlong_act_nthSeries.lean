-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/c92ca071-9c15-53bd-9a4f-1a074f0ade6d
-- title:
--   An integer prime to q acting as [n]_F
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$. Let $\mathrm{coord}:\Lambda\to\mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ (with $\mathbb{Z}_{q^2}$ the Witt vectors of $\mathbb{F}_{q^2}$) satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$ whenever $1\in\Lambda$, is multiplicative for the twisted rule $(x_1,x_2)(y_1,y_2)=(x_1y_1+q\,x_2\varphi(y_2),\,x_1y_2+x_2\varphi(y_1))$ with $\varphi$ the Witt-vector Frobenius, is injective, has image dense modulo every power of $q$, and sends $m$ with $m+\bar m=n$ to a first coordinate of trace $n$. Let $B$ be a commutative ring in which the image of $q$ is nilpotent, $E$ a fake elliptic curve over $B$ of level $N$ with $\Lambda$-action (a scheme $A\to\operatorname{Spec}B$ with commutative relative group law $L$, abelian-scheme property bundle, two-dimensional fibres, and an action `act` of $\Lambda$ by $B$-endomorphisms), $F$ a commutative $2$-dimensional formal group law over $B$, and $\theta$ formal coordinates for $E$ identifying, on nilpotent tuples over any $B$-algebra, the truncations of $F$ with $L$. Then there is $n\in\mathbb{N}$ coprime to $q$ with $(n:\mathbb{Q})\in\Lambda$, $\mathrm{coord}(n)=(n,0)$, and such that the endomorphism $\mathrm{act}(n)$ of $A$ over $\operatorname{Spec}B$ is, in the coordinates $\theta$, given by the $n$-th multiplication series $[n]_F$.
--
--   This records the unital normalisation of the $\Lambda$-action on the formal group of a fake elliptic curve: some integer prime to $q$ lies in $\Lambda$, has coordinate $(n,0)$, and acts by multiplication by $n$ on the formal group. It is used in the construction of the special formal $\mathcal{O}$-module attached to a fake elliptic curve, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates), on the Cerednik–Drinfel'd side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (F : MvFormalGroup 2 B) (hF : F.IsComm) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.L.IsFormalCoordinates F θ) :
    ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        IsFormalCompletionAlong θ θ (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩) (E.act_over _) (F.nthSeries n) := by sorry
