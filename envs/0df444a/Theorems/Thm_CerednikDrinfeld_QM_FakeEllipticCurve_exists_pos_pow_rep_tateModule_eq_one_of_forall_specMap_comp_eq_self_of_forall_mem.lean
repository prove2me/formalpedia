-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_forall_specMap_comp_eq_self_of_forall_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_forall_specMap_comp_eq_self_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c799b3ee-2923-5200-add4-b0326152a0a5
-- title:
--   Finite-order inertia on every ℓ-adic Tate module
-- statement:
--   Let $q \neq q'$ be primes, $N$ a natural number, and $a,b$ rationals such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $R$ be a discrete valuation domain with fraction field $K$, let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $K$ (a scheme $E.A$ over $\operatorname{Spec} K$ with commutative relative group law $E.L$, abelian-scheme property bundle, two-dimensional fibres, and the structure recorded in `FakeEllipticCurve`), and let $\Omega$ be an algebraic closure of $K$. Let $\ell_0$ be a prime whose image in $R$ is a unit, and $K' \subseteq \Omega$ an intermediate field finite over $K$ such that: for every valuation subring $A$ of $\Omega$ containing the image of $R$, every $\sigma$ in the inertia subgroup of $A$ inside $\Omega \simeq_{\mathrm{alg}[K]} \Omega$ fixing $K'$ pointwise, every $v$, and every $\Omega$-point $x$ of $E$ over $K$ killed by $\ell_0^v$ for $E.L$, composing $\operatorname{Spec}\sigma$ with $x$ returns $x$. Then for every prime $\ell$ whose image in $R$ is a unit, every valuation subring $A$ of $\Omega$ containing the image of $R$, and every $\sigma$ in the inertia subgroup of $A$ in $\Omega \simeq_{\mathrm{alg}[K]} \Omega$, there is $M > 0$ with $\rho_\ell(\sigma)^M = 1$, where $\rho_\ell$ is the representation on the $\ell$-adic Tate module of the group of $\Omega$-points $E.L.\mathrm{AlgPoints}\,E.comm\,\Omega$, realised as the $\mathbb{Z}_\ell$-module of sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$.
--
--   This is the Néron–Ogg–Shafarevich transfer step for fake elliptic curves: unramifiedness of the $\ell_0$-power torsion after a finite extension $K'/K$ forces every inertia element to act with finite order on all $\ell$-adic Tate modules with $\ell$ invertible in $R$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn), and rests on a Hensel-local base change of $E$ together with the criterion for an inertia element to fix torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_forall_specMap_comp_eq_self_of_forall_mem.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_forall_specMap_comp_eq_self_of_forall_mem
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ℓ₀ : ℕ) [Fact ℓ₀.Prime] (hℓ₀ : IsUnit ((ℓ₀ : ℕ) : R))
    (K' : IntermediateField K Ω) [FiniteDimensional K ↥K']
    (hK' : ∀ (A : ValuationSubring Ω), (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K → (∀ x : Ω, x ∈ K' → σ x = x) →
        ∀ (v : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) E.f),
          E.L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (ℓ₀ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ M : ℕ, 0 < M ∧ (TateModule.rep ℓ (E.L.AlgPoints E.comm Ω) (Ω ≃ₐ[K] Ω) σ) ^ M = 1 := by sorry
