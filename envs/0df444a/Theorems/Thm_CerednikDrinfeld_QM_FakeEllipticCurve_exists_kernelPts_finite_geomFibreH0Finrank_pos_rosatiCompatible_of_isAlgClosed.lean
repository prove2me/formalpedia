-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelPts_finite_geomFibreH0Finrank_pos_rosatiCompatible_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelPts_finite_geomFibreH0Finrank_pos_rosatiCompatible_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/be93c878-9ae2-55e0-a863-8fd520833fa8
-- title:
--   Existence of a ⋆-compatible polarisation on fake elliptic curves
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among the orders containing it, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be a map with $\mu\,\mathrm{star}(x)=\bar{x}\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $k$ be an algebraically closed field, and let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $k$: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, an abelian-scheme property bundle, all fibres of topological Krull dimension $2$, and an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over the base together with its compatibilities. Then there exists an $\mathcal{O}_{E.A}$-module $\mathcal{L}$ which is invertible (locally on $E.A$ isomorphic to the unit sheaf) such that: the set of base-points of $E.f$ lying in the stabiliser of $\mathcal{L}$ for $E.L$ is finite; for every algebraically closed field $k'$ and every ring homomorphism $sk:k\to k'$ the $k'$-dimension of the global sections of the pullback of $\mathcal{L}$ to the fibre over $k'$ is positive; and $\mathcal{L}$ is Rosati-compatible, that is, for each $b\in\Lambda$ the pullbacks of the Mumford bundle $\mathrm{add}^{*}\mathcal{L}\otimes p_1^{*}\mathcal{L}^{\vee}\otimes p_2^{*}\mathcal{L}^{\vee}$ along $(p_1,E.\mathrm{act}(b)\circ p_2)$ and along $(E.\mathrm{act}(\mathrm{star}\,b)\circ p_1,p_2)$ become isomorphic over the preimages of a neighbourhood of each point of the base.
--
--   This is the existence of a $\star$-compatible polarisation on an abelian surface with quaternionic multiplication by a maximal order in an indefinite quaternion algebra: the invertible sheaf obtained is non-degenerate (finite stabiliser) and effective (positive $h^0$ on all geometric fibres), and its Mumford bundle transforms under the $\Lambda$-action through the involution $\mathrm{star}$. It is the input to the later statements on fake elliptic curves over discrete valuation rings and on trivial-kernel ($\star$-compatible, principal) polarisations in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelPts_finite_geomFibreH0Finrank_pos_rosatiCompatible_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelPts_finite_geomFibreH0Finrank_pos_rosatiCompatible_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ (kernelPts E.f E.L 𝓛).Finite ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E.f 𝓛 k' sk) ∧
      RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
