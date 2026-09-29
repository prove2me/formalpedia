-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_specMap_comp_eq_self_of_forall_exists_pos_pow_rep_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_specMap_comp_eq_self_of_forall_exists_pos_pow_rep_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8dd3baaa-31f6-59e8-b130-b143c44c2f00
-- title:
--   Inertia fixes ℓ-power torsion over a finite extension
-- statement:
--   Fix natural numbers $N$ and primes $q,q'$ with $q'\neq q$, rationals $a,b$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb Q}$ every nonzero element of $\mathbb{H}[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among the orders containing it, let $R$ be a discrete valuation domain with fraction field $K$, let $E$ be a fake elliptic curve of level $N$ for $\Lambda$ over $K$ (a scheme $E.A$ over $\operatorname{Spec} K$ with commutative relative group law $E.L$, abelian-scheme bundle, fibres of dimension $2$, and a $\Lambda$-action with the prescribed trace condition), let $\Omega$ be an algebraic closure of $K$, and let $\ell$ be a prime whose image in $R$ is a unit. Assume that for every valuation subring $A$ of $\Omega$ containing the image of $R$ and every $\sigma$ in the inertia subgroup of $A$ inside $\operatorname{Aut}_K(\Omega)$, some positive power of $\rho_\ell(\sigma)$ acting on the Tate module $T_\ell$ of the group of $\Omega$-points of $E$ (sequences $(x_n)$ with $\ell^n x_n=0$, $\ell x_{n+1}=x_n$) is the identity. Then there is an intermediate field $K'$ of $\Omega/K$, finite over $K$, such that for every such $A$ and every such inertia element $\sigma$ fixing $K'$ pointwise, every $v\in\mathbb N$ and every section $x$ of $E.f$ over $\operatorname{Spec}(\Omega)\to\operatorname{Spec}(K)$ killed by $\ell^v$ for $E.L$, the composite $\operatorname{Spec}(\sigma)$ followed by $x$ equals $x$.
--
--   This is the step, in the study of fake elliptic curves over a discretely valued base, which upgrades 'inertia acts with finite order on $T_\ell$' to 'inertia acts trivially on all $\ell$-power torsion after a finite base change', in the spirit of the Serre–Tate criterion for good reduction. It is used in deducing that a power of the inertia representation on the Tate module is trivial, towards potential good reduction of the fake elliptic curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_specMap_comp_eq_self_of_forall_exists_pos_pow_rep_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open CategoryTheory AlgebraicGeometry NeronModelInfra QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_specMap_comp_eq_self_of_forall_exists_pos_pow_rep_eq_one
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R))
    (hfin : ∀ (A : ValuationSubring Ω), (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
        ∃ M : ℕ, 0 < M ∧ (TateModule.rep ℓ (E.L.AlgPoints E.comm Ω) (Ω ≃ₐ[K] Ω) σ) ^ M = 1) :
    ∃ (K' : IntermediateField K Ω) (_ : FiniteDimensional K ↥K'),
      ∀ (A : ValuationSubring Ω), (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K → (∀ x : Ω, x ∈ K' → σ x = x) →
        ∀ (v : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) E.f),
          E.L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by sorry
