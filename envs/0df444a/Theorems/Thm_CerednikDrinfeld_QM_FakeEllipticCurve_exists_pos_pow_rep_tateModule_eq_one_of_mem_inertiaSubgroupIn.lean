-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/22aefa0e-f959-5fb4-a13e-78383996be1b
-- title:
--   Inertia acts with finite order on T_ℓ of a fake elliptic curve
-- statement:
--   Fix natural numbers $N$ and two primes $q,q'$ with $q' \neq q$, and rationals $a,b$ such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is an order and is maximal among orders. Let $R$ be a discrete valuation domain with finite residue field and fraction field $K$, let $E$ be a fake elliptic curve over $K$ for $\Lambda$ and level $N$ — the structure `FakeEllipticCurve Λ N K`, packaging a scheme $A \to \operatorname{Spec} K$ with a commutative relative group law $E.L$, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and satisfying the trace condition, together with the further level data of that structure. Let $\Omega$ be an algebraic closure of $K$ and $\ell$ a prime that is a unit in $R$. Then for every valuation subring $A$ of $\Omega$ whose elements include the images of all $r \in R$, and every $\sigma \in \operatorname{Gal}(\Omega/K)$ lying in the image of the inertia subgroup of $A$ over $K$ inside the decomposition subgroup, there is an $M > 0$ with $\rho_\ell(\sigma)^M = 1$, where $\rho_\ell$ is the action of $\operatorname{Gal}(\Omega/K)$ on the $\ell$-adic Tate module of the group of $\Omega$-points $E.L.\mathrm{AlgPoints}$, i.e. on the $\mathbb{Z}_\ell$-module of sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$.
--
--   This is the Galois-theoretic form of potentially good reduction for abelian surfaces with quaternionic multiplication over a discrete valuation ring with finite residue field: inertia acts on the $\ell$-adic Tate module through a finite group. It feeds the step showing that inertia acts trivially on $\ell$-power torsion of a fake elliptic curve carrying a rational full level structure, used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ M : ℕ, 0 < M ∧ (TateModule.rep ℓ (E.L.AlgPoints E.comm Ω) (Ω ≃ₐ[K] Ω) σ) ^ M = 1 := by sorry
