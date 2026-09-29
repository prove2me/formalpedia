-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/cfa76507-1608-5745-b087-1c85a2d9b082
-- title:
--   Uniqueness of the canonical polarisation over a local base
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such orders; let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \cdot \mu$ for all $x \in \Lambda$, where $\bar{\phantom{x}}$ is quaternion conjugation. Let $N$ be a natural number and $S$ a local commutative ring in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} S$, a commutative relative group law $E.L$, smooth and proper with connected fibres, all fibres of dimension $2$, together with the $\Lambda$-action $E.\mathrm{act}$ over the base compatible with the group law and the trace condition, and the remaining level data. Let $\mathcal{L}$ and $\mathcal{L}'$ be two modules on $E.A$ each of which is a canonical polarisation datum for $\mathrm{star}$, i.e. invertible, symmetric, with kernel killed by $2$, with positive $h^0$ on all geometric fibres, Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$, and admitting, after some faithfully flat extension $S \to S'$, a square root: an invertible module $\mathcal{L}_0$ with trivial kernel whose pullback's tensor product with its pullback along inversion is isomorphic, locally on the base, to the pullback of the datum. The conclusion is `LocIsoOnBase E.f 𝓛 𝓛'`: every point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that the restrictions of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic. (As $S$ is local, one may take $U = \operatorname{Spec} S$.)
--
--   This is the uniqueness of the canonical polarisation datum on a fake elliptic curve over a local base, in the edition assuming $2$ invertible in the base; it is the local case from which the statement over an arbitrary base is obtained by base change to the local rings of the base. It is used by the corresponding result [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two) over a general base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) [IsLocalRing S] (E : FakeEllipticCurve Λ N S)
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
