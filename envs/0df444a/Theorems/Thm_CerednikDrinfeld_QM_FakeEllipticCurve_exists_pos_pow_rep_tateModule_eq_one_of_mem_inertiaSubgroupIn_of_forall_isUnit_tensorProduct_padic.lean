-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b73f9370-5904-5803-9b45-bd76cb7c8cea
-- title:
--   Finite inertia order on T_ℓ of a fake elliptic curve
-- statement:
--   Fix natural numbers $N, q, q'$ with $q, q'$ prime and $q' \neq q$, rationals $a, b$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element a unit) exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $R$ be a discrete valuation domain with finite residue field and fraction field $K$, and let $E$ be a `FakeEllipticCurve Λ N K`: a scheme $A$ over $\operatorname{Spec} K$ carrying a commutative relative group law $E.L$, an abelian-scheme property bundle, all fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative, compatible with the group law, satisfies the trace condition on tangent spaces, and the further level data of the structure. Let $\Omega$ be an algebraic closure of $K$, and $\ell$ a prime which is a unit in $R$ and such that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_\ell$ is a unit. Let $A$ be a valuation subring of $\Omega$ containing the image of $R$, and let $\sigma \in \operatorname{Gal}(\Omega/K)$ lie in `inertiaSubgroupIn`, the image in $\operatorname{Gal}(\Omega/K)$ of the inertia subgroup of $A$ over $K$. Then there is $M > 0$ such that the $\mathbb{Z}_\ell$-linear endomorphism by which $\sigma$ acts on the Tate module $T_\ell$ of the group of $\Omega$-points `E.L.AlgPoints E.comm Ω` — the group of sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$ — satisfies $\rho_\ell(\sigma)^M = 1$.
--
--   This is the statement that inertia acts with finite order on the $\ell$-adic Tate module of a fake elliptic curve over a discrete valuation ring with finite residue field, in the case of a prime $\ell$ at which the quaternion algebra is a division algebra. It is the special case from which the version for an arbitrary prime unit $\ell$, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn), is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn_of_forall_isUnit_tensorProduct_padic
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ M : ℕ, 0 < M ∧ (TateModule.rep ℓ (E.L.AlgPoints E.comm Ω) (Ω ≃ₐ[K] Ω) σ) ^ M = 1 := by sorry
