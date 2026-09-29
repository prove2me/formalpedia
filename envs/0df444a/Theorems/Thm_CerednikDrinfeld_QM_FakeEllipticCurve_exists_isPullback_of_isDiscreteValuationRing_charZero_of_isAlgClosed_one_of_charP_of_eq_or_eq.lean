-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_eq_or_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_eq_or_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/f93dbea4-bdba-5663-8cde-2453fb7a63c6
-- title:
--   Lifting level-one fake elliptic curves in residue characteristic q or q'
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\operatorname{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\operatorname{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$, where $\bar{\phantom{x}}$ is quaternionic conjugation. Let $k$ be an algebraically closed field of characteristic a prime $p$ with $p=q$ or $p=q'$, and let $E$ be a fake elliptic curve over $k$ with $\Lambda$-action and level parameter $N=1$, i.e. an abelian scheme datum $E.A\to\operatorname{Spec} k$ with commutative relative group law, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base satisfying the trace condition, and the level datum $E.C\to E.A$. Then there exist a type $R$ carrying a commutative ring structure which is a domain, a discrete valuation ring and of characteristic zero, and a ring homomorphism $\varphi:R\to k$, such that $\varphi$ is surjective, $R$ is complete for the adic topology of its maximal ideal, and there is a fake elliptic curve $E_R$ over $R$ with $\Lambda$-action and level parameter $1$ satisfying `FakeEllipticCurve.IsPullback` $\varphi$ $E_R$ $E$: there is a morphism $g:E.A\to E_R.A$ making $E.A$ the fibre product of $E_R.A$ with $\operatorname{Spec} k$ over $\operatorname{Spec} R$ along $\operatorname{Spec}\varphi$, compatible with the two relative group laws on points over any base, equivariant for the $\Lambda$-actions, and such that any point of $E$ factoring through $E.\mathrm{lev}$ has its image under $g$ factoring through $E_R.\mathrm{lev}$.
--
--   This is the lifting of a level-one fake elliptic curve from an algebraically closed field to a complete discrete valuation ring of characteristic zero with that residue field, in the case where the residue characteristic is one of the two ramified primes $q,q'$ of the indefinite quaternion algebra; the formal moduli of the associated special formal $\mathcal{O}_D$-module replace ordinary Serre–Tate theory here. It feeds, together with the complementary cases, into [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_isUnit_two) in the Čerednik–Drinfel'd uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_eq_or_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_eq_or_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : p = q ∨ p = q')
    (E : FakeEllipticCurve Λ 1 k) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R) (φ : R →+* k),
      Function.Surjective φ ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ∃ E_R : FakeEllipticCurve Λ 1 R, FakeEllipticCurve.IsPullback φ E_R E := by sorry
