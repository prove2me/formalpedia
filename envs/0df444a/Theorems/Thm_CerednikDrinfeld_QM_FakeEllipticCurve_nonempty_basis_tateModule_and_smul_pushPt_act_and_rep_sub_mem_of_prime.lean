-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_basis_tateModule_and_smul_pushPt_act_and_rep_sub_mem_of_prime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_basis_tateModule_and_smul_pushPt_act_and_rep_sub_mem_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ca976260-d1e7-598c-8116-67134e6d5533
-- title:
--   Tate module of a fake elliptic curve: rank four, equivariant, continuous
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a field $K$, and a fake elliptic curve $E$ of type `FakeEllipticCurve Λ N K`: a scheme $E.A$ with a morphism $E.f$ to $\operatorname{Spec} K$, a relative group law $E.L$ on the functor of points of $E.f$ which is commutative ($E.comm$), an abelian-scheme property bundle, fibres of topological Krull dimension $2$, endomorphisms $E.act\,m$ of $E.A$ over $\operatorname{Spec} K$ for $m \in \Lambda$ which are additive for the group law and compatible with the ring structure of $\Lambda$ up to reversal, a trace condition on tangent spaces, and a level-$N$ datum. Let $\Omega$ be an algebraically closed field that is an algebraic $K$-algebra, and let $\ell$ be a prime with $\ell \neq 0$ in $K$. Write $M = E.L.AlgPoints\,E.comm\,\Omega$ for the additive group of $\Omega$-points of $E.f$, on which $\operatorname{Aut}_K(\Omega)$ acts, and $T_\ell =$ [`TateModule ℓ M`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $M$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, a $\mathbb{Z}_\ell$-module. The conclusion is threefold: (i) $T_\ell$ admits a $\mathbb{Z}_\ell$-basis indexed by `Fin 4`; (ii) for every $\sigma \in \operatorname{Aut}_K(\Omega)$, every $m \in \Lambda$ and every $P \in M$, one has $\sigma \cdot (E.act\,m \circ P) = E.act\,m \circ (\sigma \cdot P)$, where $E.act\,m \circ P$ denotes `pushPt`, post-composition of the $\Omega$-point with the endomorphism; and (iii) for every $n$ there is an intermediate field $L$ of $\Omega/K$, finite-dimensional over $K$, such that every $\sigma$ fixing $L$ pointwise satisfies $\mathrm{rep}(\sigma)v - v \in (\mathfrak{m}_{\mathbb{Z}_\ell}^{\,n}) \cdot T_\ell$ for all $v \in T_\ell$, where $\mathrm{rep}$ is the levelwise action of $\operatorname{Aut}_K(\Omega)$ on $T_\ell$.
--
--   These are the three formal properties making the $\ell$-adic Tate module of a fake elliptic curve over $K$ a continuous four-dimensional $\ell$-adic representation of $\operatorname{Aut}_K(\Omega)$ commuting with the action of $\Lambda$, the standard input for Néron–Ogg–Shafarevich-type and monodromy arguments. It is used in the study of inertia action and potentially good reduction for fake elliptic curves, in particular by the statements on finite-order and unipotent behaviour of $\mathrm{rep}$ on inertia subgroups and on full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_basis_tateModule_and_smul_pushPt_act_and_rep_sub_mem_of_prime.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_basis_tateModule_and_smul_pushPt_act_and_rep_sub_mem_of_prime
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (Module.Basis (Fin 4) ℤ_[ℓ] (TateModule ℓ (E.L.AlgPoints E.comm Ω))) ∧
    (∀ (σ : Ω ≃ₐ[K] Ω) (m : ↥Λ) (P : E.L.AlgPoints E.comm Ω),
      σ • (RelativeGroupLaw.AlgPoints.ofPoint
          (pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint P)) : E.L.AlgPoints E.comm Ω) =
        RelativeGroupLaw.AlgPoints.ofPoint
          (pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint (σ • P)))) ∧
    (∀ n : ℕ, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
      ∀ σ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = x) →
        ∀ v : TateModule ℓ (E.L.AlgPoints E.comm Ω),
          TateModule.rep ℓ (E.L.AlgPoints E.comm Ω) (Ω ≃ₐ[K] Ω) σ v - v ∈
            (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) • (⊤ : Submodule ℤ_[ℓ] (TateModule ℓ (E.L.AlgPoints E.comm Ω)))) := by sorry
