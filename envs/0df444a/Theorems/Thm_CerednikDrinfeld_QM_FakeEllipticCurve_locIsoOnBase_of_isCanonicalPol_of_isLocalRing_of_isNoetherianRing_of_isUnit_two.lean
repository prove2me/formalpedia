-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isNoetherianRing_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isNoetherianRing_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/347d0aaa-8aa3-518f-bdf6-cbed534a4667
-- title:
--   Uniqueness of canonical polarisation data over local noetherian bases
-- statement:
--   Let $q \neq q'$ be primes and let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated; and it is maximal among orders for inclusion), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\star : \Lambda \to \Lambda$ be a map with $\mu \cdot \star(x) = \bar{x}\,\mu$ for all $x \in \Lambda$, where $\bar{\;}$ is quaternionic conjugation. Let $N \in \mathbb{N}$ and let $S$ be a commutative ring which is local, noetherian, and in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data, with structure morphism $E.f : E.A \to \operatorname{Spec} S$. Let $\mathcal{L}, \mathcal{L}'$ be modules on $E.A$ which both satisfy `E.IsCanonicalPol star`, that is, each is invertible, symmetric for the relative group law, has kernel contained in the $2$-torsion, becomes (after a faithfully flat base change on $S$) locally on the base a square $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$ with trivial kernel, has positive $H^0$ on geometric fibres, and is Rosati-compatible with the $\Lambda$-action and $\star$. Then $\mathcal{L}$ and $\mathcal{L}'$ are locally isomorphic over the base: for every point $s$ of $\operatorname{Spec} S$ there is an open neighbourhood $U$ of $s$ such that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic.
--
--   This is the uniqueness half of the canonical (Rosati-compatible) polarisation datum on a fake elliptic curve, here over an arbitrary local noetherian base in which $2$ is invertible; it is the statement needed to make the polarisation a well-defined part of the moduli problem for the Cherednik–Drinfeld uniformisation of Shimura curves. It feeds the comparison of canonical polarisation data with their square roots, `locIsoOnBase_of_isCanonicalPol_of_locIsoOnBase_sqrt_of_isLocalRing_of_isUnit_two`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isNoetherianRing_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isLocalRing_of_isNoetherianRing_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) [IsLocalRing S] [IsNoetherianRing S] (E : FakeEllipticCurve Λ N S)
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
