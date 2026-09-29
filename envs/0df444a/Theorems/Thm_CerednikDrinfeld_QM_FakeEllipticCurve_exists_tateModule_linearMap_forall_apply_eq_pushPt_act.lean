-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_linearMap_forall_apply_eq_pushPt_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/1501b33f-5a0c-570c-b736-f098ffb0fa09
-- title:
--   Λ acts ℤ_ℓ-linearly on the Tate module
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a field $K$, and a fake elliptic curve $E$ of type `FakeEllipticCurve Λ N K`: thus a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} K$, a relative group law $L$ on $f$ which is commutative (`E.comm`), the smoothness/properness/connected-fibre bundle and two-dimensional fibres, together with endomorphisms $\mathrm{act}(m) : A \to A$ for $m \in \Lambda$ commuting with $f$ and satisfying the compatibilities `act_hom`, `act_one`, `act_mul` (in diagrammatic order: $\mathrm{act}(mm') = \mathrm{act}(m')$ followed by $\mathrm{act}(m)$), `act_add` and the trace condition, plus the auxiliary curve data. Let $\Omega$ be a field equipped with a $K$-algebra structure and $\ell$ a prime. Write $A(\Omega) =$ `E.L.AlgPoints E.comm Ω` for the group of $\Omega$-points, that is, the additive group of morphisms $\operatorname{Spec}\Omega \to A$ over $\operatorname{Spec} K$ with the group law $L$, and $T_\ell A(\Omega) =$ [`TateModule ℓ (E.L.AlgPoints E.comm Ω)`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)_{n \in \mathbb{N}}$ of $\Omega$-points with $\ell^n x_n = 0$ and $\ell\, x_{n+1} = x_n$, a $\mathbb{Z}_\ell$-module. The assertion is that there is a family $\rho$ of $\mathbb{Z}_\ell$-linear endomorphisms $\rho(m)$ of $T_\ell A(\Omega)$, indexed by $m \in \Lambda$, such that: for all $m$, $v$ and $n$ the $n$-th level of $\rho(m)v$ is the $\Omega$-point underlying $v_n$ followed by $\mathrm{act}(m)$; $\rho(1) = \mathrm{id}$ whenever $1 \in \Lambda$; $\rho(mm') = \rho(m) \circ \rho(m')$ whenever $mm' \in \Lambda$; and $\rho(m+m') = \rho(m) + \rho(m')$.
--
--   This provides the $\ell$-adic representation of the quaternionic order $\Lambda$ on the Tate module of a fake elliptic curve, in the form of a levelwise-described, unital, multiplicative and additive family of $\mathbb{Z}_\ell$-linear endomorphisms. It is the input $(\rho, \rho_1, \rho_{\mathrm{mul}}, \rho_{\mathrm{add}})$ used downstream in the study of the $\star$-alternating pairing and triviality of kernels on Tate modules of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_linearMap_forall_apply_eq_pushPt_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ρ : ↥Λ → (TateModule ℓ (E.L.AlgPoints E.comm Ω) →ₗ[ℤ_[ℓ]] TateModule ℓ (E.L.AlgPoints E.comm Ω)),
      (∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
        RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n) =
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n))) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id) ∧
      (∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m ∘ₗ ρ m') ∧
      (∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m') := by sorry
