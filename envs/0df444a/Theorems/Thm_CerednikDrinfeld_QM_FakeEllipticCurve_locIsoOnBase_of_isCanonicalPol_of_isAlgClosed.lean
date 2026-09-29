-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ef1c2d5e-8f06-5b09-ab25-af3d975c4cb9
-- title:
--   Uniqueness of the canonical polarisation over ̄ k
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$: either $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, that is, an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning $B$, finitely generated) maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\star:\Lambda\to\Lambda$ satisfy $\mu\,\star(x)=\bar x\,\mu$ for all $x\in\Lambda$. Fix $N\in\mathbb{N}$, an algebraically closed field $k$, and a fake elliptic curve $E$ of level $N$ over $k$ with $\Lambda$-action, i.e. a `FakeEllipticCurve Λ N k`: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, the abelian-scheme property bundle (smooth, proper, connected fibres, group law), fibres of topological Krull dimension $2$, and an action $E.act$ of $\Lambda$ over the base which is additive, multiplicative and satisfies the prescribed trace condition on tangent spaces. Let $\mathcal{L},\mathcal{L}'$ be objects of $E.A$-modules each satisfying `E.IsCanonicalPol star`, namely `IsCanonicalPolData` for $E.f,E.L,E.act,E.act\_over,\star$: invertible, symmetric for the group law, with kernel killed by $2$, admitting after a faithfully flat base change $k\to S'$ an invertible square root with trivial kernel in the sense that the pullback is locally on the base isomorphic to $\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$, having positive $H^{0}$-rank on all geometric fibres, and Rosati-compatible with the $\Lambda$-action. The conclusion is `LocIsoOnBase E.f 𝓛 𝓛'`: every point $s$ of $\operatorname{Spec} k$ has an open neighbourhood $U$ such that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic.
--
--   This is the uniqueness half of the statement that a fake elliptic curve over an algebraically closed field carries a canonical polarisation: any two line bundles satisfying the canonical-polarisation conditions agree, locally on the base and hence (the base being the spectrum of a field) globally. It is used by the variant of the result formulated under the hypothesis that $2$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (𝓛 𝓛' : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛) (h𝓛' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
