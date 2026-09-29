-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_iso_of_isCanonicalPol_of_isAdicComplete_of_isAlgClosed_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_iso_of_isCanonicalPol_of_isAdicComplete_of_isAlgClosed_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5b513429-b972-574d-a28d-335022d3fde7
-- title:
--   Uniqueness of canonical polarisation data over a complete local base
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: one of $a,b$ is positive, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (it contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, is finitely generated, and admits no strictly larger order), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\star : \Lambda \to \Lambda$ satisfy $\mu \cdot \star x = \bar{x} \cdot \mu$ for all $x \in \Lambda$, where $\bar{\ }$ is quaternion conjugation. Let $N$ be a natural number and $R$ a commutative ring in which $2$ is a unit, local, noetherian, complete for the adic topology of its maximal ideal, and with algebraically closed residue field. Let $E$ be a fake elliptic curve over $R$ with $\Lambda$-action and level $N$ (a smooth proper scheme $E.A \to \operatorname{Spec} R$ with connected fibres of dimension $2$, a commutative relative group law $E.L$, a $\Lambda$-action $E.act$ by morphisms over the base which is additive and multiplicative and satisfies the trace condition, together with the curve data). Let $\mathcal{L}, \mathcal{L}'$ be objects of $E.A.Modules$, each a canonical polarisation datum for $\star$, that is: invertible, symmetric for $E.L$, with kernel contained in the $2$-torsion, satisfying the descent condition that over some faithfully flat $R$-algebra $S'$ the pullback of the module is locally isomorphic on the base to $\mathcal{L}_0 \otimes [-1]^{*}\mathcal{L}_0$ for some invertible $\mathcal{L}_0$ with trivial kernel (for every relative group law on the pullback compatible with $E.L$), having strictly positive $H^0$ rank on every geometric fibre, and Rosati-compatible with $E.act$ and $\star$. Then $\mathcal{L}$ and $\mathcal{L}'$ are isomorphic in $E.A.Modules$.
--
--   This is the uniqueness half of the canonical polarisation on a fake elliptic curve: over a complete local noetherian base with algebraically closed residue field, and with $2$ invertible, any two canonical polarisation data are isomorphic. It is obtained from the corresponding statement on the algebraically closed residue field, lifted successively along the Artinian thickenings $R/\mathfrak{m}^{k+1}$ and then over the complete base, and is used in the form asserting local isomorphism on the base over an arbitrary local noetherian ring, en route to the rigidity and representability statements for the quaternionic moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_iso_of_isCanonicalPol_of_isAdicComplete_of_isAlgClosed_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_iso_of_isCanonicalPol_of_isAdicComplete_of_isAlgClosed_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (R : Type) [CommRing R] (h2 : IsUnit (2 : R)) [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (E : FakeEllipticCurve Λ N R)
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛') :
    Nonempty (𝓛 ≅ 𝓛') := by sorry
