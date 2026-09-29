-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2c992d33-f4c6-5d41-91dd-b97ea37c4cbc
-- title:
--   Uniqueness of canonical polarisation data over any affine base
-- statement:
--   Fix two rational primes $q,q'$ with $q'\neq q$, and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order — containing $1$, closed under multiplication, $\mathbb{Q}$-spanning the algebra, finitely generated — maximal among orders containing it), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be a map with $\mu\cdot\mathrm{star}(x)=\bar{x}\,\mu$ for all $x\in\Lambda$. Let $N$ be a natural number, $S$ a commutative ring in which $2$ is a unit, and $E$ a fake elliptic curve of level $N$ over $S$ for $\Lambda$ (an abelian scheme $E.f : E.A\to\operatorname{Spec} S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base, and the further data recorded in `FakeEllipticCurve`). Let $\mathcal{L},\mathcal{L}'$ be objects of `E.A.Modules` each satisfying `E.IsCanonicalPol star`, that is: invertibility, symmetry and two-torsion kernel for the relative group law, existence of a faithfully flat base extension $S\to S'$ over which $\mathcal{L}$ becomes, locally on the base, the tensor product of an invertible module with trivial kernel and its pullback along the inversion, positivity of the geometric fibre $H^0$ rank at every algebraically closed residue field, and Rosati-compatibility of the $\Lambda$-action with $\mathrm{star}$. Then `LocIsoOnBase E.f` $\mathcal{L}$ $\mathcal{L}'$ holds: every point $s\in\operatorname{Spec} S$ has an open neighbourhood $U$ such that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic.
--
--   This is the uniqueness half of the canonical (Drinfeld) polarisation on a fake elliptic curve, here over an arbitrary affine base in which $2$ is invertible, with uniqueness asserted only locally on the base. It is used in the existence-and-uniqueness statement for canonical polarisation data and in the comparison of polarised abelian schemes with quaternionic multiplication and full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
