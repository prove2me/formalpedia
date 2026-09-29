-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/87cf9e50-120c-575a-b95d-2147b3c7c2d6
-- title:
--   Uniqueness of the canonical polarisation over an algebraically closed field
-- statement:
--   Let $q,q'$ be primes with $q' \neq q$, and let $a,b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, that is, $1 \in \Lambda$, $\Lambda$ is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is maximal among such orders. Let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$, where $\bar{\;\cdot\;}$ is quaternionic conjugation. Let $N$ be a natural number, $k$ an algebraically closed field with $2 \neq 0$ in $k$, and $E$ a fake elliptic curve of level $N$ for $\Lambda$ over $k$, i.e. a scheme $E.A$ over $\operatorname{Spec} k$ with a commutative relative group law, smooth proper with connected fibres, fibres of dimension $2$, carrying an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative and satisfies the trace condition, together with the remaining data of the structure. Let $\mathcal{L}, \mathcal{L}'$ be modules on $E.A$, each a canonical polarisation for $\mathrm{star}$ in the sense of `IsCanonicalPolData`: invertible, symmetric, with kernel killed by $2$, admitting after a faithfully flat base change $k \to S'$ a square root $\mathcal{L}_0$ (with trivial kernel) in the sense that the pullback of $\mathcal{L}$ is locally on the base isomorphic to $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$, with positive geometric fibre $H^0$-rank at every algebraically closed field point, and Rosati-compatible with the $\Lambda$-action and $\mathrm{star}$. Then `LocIsoOnBase E.f 𝓛 𝓛'` holds: every point $s$ of $\operatorname{Spec} k$ has an open neighbourhood $U$ such that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic; as $\operatorname{Spec} k$ is a single point this says that $\mathcal{L}$ and $\mathcal{L}'$ are isomorphic.
--
--   The statement expresses uniqueness, up to isomorphism, of the canonical (Rosati-compatible) polarisation of a fake elliptic curve over an algebraically closed field; such a uniqueness statement is what makes the canonical polarisation part of the moduli problem for quaternionic multiplication rather than extra data. It is used in the passage to complete local bases, in the construction of isomorphisms between canonical polarisations over adically complete rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_isAlgClosed_of_two_ne_zero.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed_of_two_ne_zero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (h2 : (2 : k) ≠ 0)
    (𝓛 𝓛' : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛) (h𝓛' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
