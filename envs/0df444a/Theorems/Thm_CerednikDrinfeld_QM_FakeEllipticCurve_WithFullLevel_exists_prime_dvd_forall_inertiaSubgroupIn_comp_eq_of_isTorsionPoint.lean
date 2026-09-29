-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_prime_dvd_forall_inertiaSubgroupIn_comp_eq_of_isTorsionPoint
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_prime_dvd_forall_inertiaSubgroupIn_comp_eq_of_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a5d7d0ac-afac-510b-bef1-14b1b2c1b411
-- title:
--   Inertia fixes ℓ-power torsion of full-level fake elliptic curves
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among the orders containing it, let $N$ be a natural number and let $m\geq 3$. Let $R$ be a discrete valuation domain with finite residue field in which the image of $m$ is a unit, let $K$ be a fraction field of $R$, let $u=(E,P)$ consist of a fake elliptic curve $E$ over $K$ with $\Lambda$-action and level-$N$ data together with a full level-$m$ structure on $E$ in the sense of `FullLevel` (a section $P$ of $E.f$ killed by $m$ which generates the $m$-torsion over every algebraically closed field under the $\Lambda$-action, with annihilator $m\Lambda$), and let $\Omega$ be an algebraic closure of $K$. Then there is a prime $\ell$ dividing $m$ with the following property: for every valuation subring $A$ of $\Omega$ containing the image of $R$, every $\sigma\in\mathrm{Gal}(\Omega/K)$ lying in `inertiaSubgroupIn` of $A$ over $K$ (the image of the inertia subgroup of $A$ inside the decomposition subgroup), every $v\in\mathbb{N}$ and every $\Omega$-point $x$ of $E$ over $\mathrm{Spec}\,K$ (a morphism to $E.A$ whose composite with $E.f$ is $\mathrm{Spec}$ of $K\to\Omega$) satisfying $\ell^{v}x=0$ for the relative group law $E.L$, the point $x$ is fixed by $\sigma$: the morphism $\mathrm{Spec}\,\sigma$ followed by $x$ equals $x$.
--
--   This is the Galois-theoretic input to the Néron–Ogg–Šafarevič criterion in this development: the existence of one prime $\ell\mid m$ whose $\ell$-power torsion is pointwise inertia-invariant. It is used in the proof that a fake elliptic curve with full level-$m$ structure over the fraction field of such a discrete valuation ring extends over the ring itself ([`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_prime_dvd_forall_inertiaSubgroupIn_comp_eq_of_isTorsionPoint.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_prime_dvd_forall_inertiaSubgroupIn_comp_eq_of_isTorsionPoint
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {m : ℕ} (hm : 3 ≤ m)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] (hmu : IsUnit ((m : ℕ) : R))
    (u : FakeEllipticCurve.WithFullLevel Λ N m K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ℓ ∣ m),
      ∀ (A : ValuationSubring Ω), (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) u.1.f),
        u.1.L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (ℓ ^ v) x →
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by sorry
