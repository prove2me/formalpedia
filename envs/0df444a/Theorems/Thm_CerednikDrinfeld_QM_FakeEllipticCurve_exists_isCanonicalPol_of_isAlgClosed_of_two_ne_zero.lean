-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9825d0ff-4667-5da5-be1e-a9ae02924147
-- title:
--   Canonical polarisation datum on a fake elliptic curve over an algebraically closed field
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the base change of $\mathbb{H}[\mathbb{Q},a,b]$ to the $v$-adic completion of $\mathbb{Q}$ has all nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning and finitely generated) and is maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be a map with $\mu\cdot\mathrm{star}(x)=\bar{x}\cdot\mu$ for all $x\in\Lambda$, where $\bar{\;}$ is quaternionic conjugation. Let $N\in\mathbb{N}$, let $k$ be an algebraically closed field with $2\neq 0$ in $k$, and let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $k$, that is, a scheme $E.A$ over $\operatorname{Spec} k$ carrying a commutative relative group law, the abelian-scheme bundle (smooth, proper, connected fibres, a group law), fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and satisfying the trace condition on tangent spaces, together with its curve and level data. Then, first, there exists a module $\mathcal{L}$ on $E.A$ which is a canonical polarisation datum for $\mathrm{star}$: it is invertible, symmetric and its kernel is $2$-torsion for the group law, there is a faithfully flat base change $k\to S'$ over which, for every compatible relative group law on the pullback, the pullback of $\mathcal{L}$ is isomorphic locally on the base to $\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$ for some invertible $\mathcal{L}_0$ with trivial kernel, the geometric fibre $H^{0}$ has positive rank over every algebraically closed field, and it is Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$; and second, any two such modules $\mathcal{L},\mathcal{L}'$ are isomorphic locally on the base, in the sense that every point of $\operatorname{Spec} k$ has an open neighbourhood $U$ whose preimage under $E.f$ carries an isomorphism between the restrictions of $\mathcal{L}$ and $\mathcal{L}'$.
--
--   This fixes the canonical polarisation $\mathcal{L}_E=\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$ attached to a fake elliptic curve with quaternionic multiplication at a geometric point, together with its uniqueness up to local isomorphism on the base, so that the polarisation is pinned rather than taken modulo pullbacks from the base. It feeds the construction of fake elliptic curves with full endomorphism dictionary used in the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isCanonicalPol_of_isAlgClosed_of_two_ne_zero.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (h2 : (2 : k) ≠ 0) :
    (∃ 𝓛 : E.A.Modules, E.IsCanonicalPol star 𝓛) ∧
    (∀ 𝓛 𝓛' : E.A.Modules, E.IsCanonicalPol star 𝓛 → E.IsCanonicalPol star 𝓛' → LocIsoOnBase E.f 𝓛 𝓛') := by sorry
