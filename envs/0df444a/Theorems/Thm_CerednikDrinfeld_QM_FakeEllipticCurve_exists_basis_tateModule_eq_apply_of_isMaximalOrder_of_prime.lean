-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_basis_tateModule_eq_apply_of_isMaximalOrder_of_prime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_basis_tateModule_eq_apply_of_isMaximalOrder_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b506b116-d768-59f9-9737-dcd5e7de32d4
-- title:
--   Tate module of a fake elliptic curve: Λ-generated ℤ_ℓ-basis
-- statement:
--   Fix rationals $a,b$ and primes $q,q'$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule that is a maximal order, in the sense that it is an order and the only order containing it is itself; let $N$ be a natural number, $K$ a field, and $E$ a fake elliptic curve of level $N$ with $\Lambda$-action over $K$: a scheme $A$ over $\operatorname{Spec} K$ with a commutative relative group law, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action `E.act` of $\Lambda$ by endomorphisms over the base compatible with the group law, additive and multiplicative in $\Lambda$, satisfying the trace condition, together with its level structure. Let $\Omega$ be an algebraically closed field which is a $K$-algebra, and $\ell$ a prime with $(\ell:K)\neq 0$. Write $M=\Lambda$'s target $E.L.AlgPoints$ $E.comm$ $\Omega$ for the additive group of $\Omega$-points of $A$ over $K$, and [`TateModule ℓ M`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)_{n\in\mathbb{N}}$ in $M$ with $\ell^n x_n=0$ and $\ell x_{n+1}=x_n$. Suppose given maps $\rho(m)$, for $m\in\Lambda$, that are $\mathbb{Z}_\ell$-linear endomorphisms of this Tate module and realise the action levelwise: for all $m$, $v$ and $n$, the point underlying the $n$-th component of $\rho(m)v$ is the pushforward along `E.act m` of the point underlying the $n$-th component of $v$. Then there exist a type $\iota$ with a `Fintype` structure, a $\mathbb{Z}$-basis $(\lambda_j)_{j\in\iota}$ of $\Lambda$, an element $x$ of the Tate module and a $\mathbb{Z}_\ell$-basis $(b_j)_{j\in\iota}$ of the Tate module, indexed by the same $\iota$, such that $b_j=\rho(\lambda_j)x$ for every $j$.
--
--   This is the freeness of rank one of the $\ell$-adic Tate module of a fake elliptic curve over $\Lambda\otimes_{\mathbb{Z}}\mathbb{Z}_\ell$, expressed concretely: a single $x$ whose translates under a $\mathbb{Z}$-basis of the maximal order form a $\mathbb{Z}_\ell$-basis of $T_\ell$. It feeds the analysis of kernels and of polarisation isomorphisms for fake elliptic curves, being used in [`CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero) and [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_basis_tateModule_eq_apply_of_isMaximalOrder_of_prime.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_basis_tateModule_eq_apply_of_isMaximalOrder_of_prime
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0)
    (ρ : ↥Λ → (TateModule ℓ (E.L.AlgPoints E.comm Ω) →ₗ[ℤ_[ℓ]] TateModule ℓ (E.L.AlgPoints E.comm Ω)))
    (hρ : ∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
      RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n) =
        pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n))) :
    ∃ (ι : Type) (_ : Fintype ι) (bΛ : Module.Basis ι ℤ ↥Λ) (x : TateModule ℓ (E.L.AlgPoints E.comm Ω))
      (bM : Module.Basis ι ℤ_[ℓ] (TateModule ℓ (E.L.AlgPoints E.comm Ω))),
      ∀ j : ι, bM j = ρ (bΛ j) x := by sorry
