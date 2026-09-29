-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/6b845c0b-4b58-5000-9144-e3486cd81833
-- title:
--   Uniqueness of canonical polarisation data, local-to-global reduction
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a, b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$, finitely generated) and is maximal among orders containing it; let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $N : \mathbb{N}$, let $S$ be a commutative ring in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ with multiplications by $\Lambda$ and level structure of level $N$ (a smooth proper morphism $E.f$ with connected two-dimensional fibres, a commutative relative group law, a $\Lambda$-action over the base compatible with the group law and satisfying the trace condition, together with the remaining level data). Assume `hloc`: for every local commutative ring $R$ in which $2$ is a unit, every fake elliptic curve $E_1$ over $R$ for the same $\Lambda$ and $N$, and any two modules $\mathcal{M}, \mathcal{M}'$ on $E_1.A$ which are both canonical polarisation data for $\mathrm{star}$ — that is, invertible, symmetric, with kernel two-torsion, satisfying the descent clause over some faithfully flat $R$-algebra asserting that the pullback is locally isomorphic to $\mathcal{L}_0 \otimes [-1]^*\mathcal{L}_0$ for an invertible module with trivial kernel, having positive geometric fibre $H^0$-rank over every algebraically closed field, and Rosati-compatible with the action and $\mathrm{star}$ — one has `LocIsoOnBase` for $E_1.f$. Then for any two canonical polarisation data $\mathcal{L}, \mathcal{L}'$ on $E.A$ the conclusion `LocIsoOnBase E.f 𝓛 𝓛'` holds: every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that the restrictions of $\mathcal{L}$ and $\mathcal{L}'$ to $E.f^{-1}(U)$ are isomorphic.
--
--   This is the local-to-global step in the uniqueness of the canonical polarisation on a fake elliptic curve (Drinfeld; Boutot–Carayol): uniqueness over local bases, assumed here as a hypothesis, is spread out to an arbitrary affine base by base change to the local rings $S_{\mathfrak{p}}$ and descent of an isomorphism to a basic open neighbourhood. It is cited by the unconditional statement [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isUnit_two); the proof uses the base-change packaging [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff), the transport of canonical polarisation data [`CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback), the spreading-out lemma [`AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime), and [`AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing`](thm.html#AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (E : FakeEllipticCurve Λ N S)
    (hloc : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsUnit (2 : R) →
      ∀ (E₁ : FakeEllipticCurve Λ N R) (𝓜 𝓜' : E₁.A.Modules),
      E₁.IsCanonicalPol star 𝓜 → E₁.IsCanonicalPol star 𝓜' → LocIsoOnBase E₁.f 𝓜 𝓜')
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛') :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
