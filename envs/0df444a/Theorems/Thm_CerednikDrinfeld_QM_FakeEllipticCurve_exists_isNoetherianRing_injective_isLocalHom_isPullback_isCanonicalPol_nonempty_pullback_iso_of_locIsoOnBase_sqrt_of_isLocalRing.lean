-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/4209c20f-5b9b-572d-92d8-d802546df059
-- title:
--   Descent of canonical polarisation data to a local Noetherian stage
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $R$ be a local commutative ring and let $E$ be a fake elliptic curve over $R$ for $\Lambda$ and $N$ (an abelian scheme $E.f:E.A\to\operatorname{Spec}R$ of relative dimension two with commutative relative group law $E.L$, a $\Lambda$-action over the base satisfying the trace condition, and the level data). Let $\mathcal{M},\mathcal{M}'$ be modules on $E.A$ satisfying `IsCanonicalPolData` for $E.f$, $E.L$, the action and $\mathrm{star}$, and let $\mathcal{M}_0,\mathcal{M}_0'$ be invertible modules (locally on $E.A$ isomorphic to the unit) whose Mumford bundle detects only the identity section, in the sense of `KernelTrivial` for $E.f$ and $E.L$. Assume $\mathcal{M}$ is isomorphic to $\mathcal{M}_0\otimes[-1]^*\mathcal{M}_0$ locally over the base, that is, every point of $\operatorname{Spec}R$ has a neighbourhood $U$ over whose preimage the two modules become isomorphic, and likewise $\mathcal{M}'$ for $\mathcal{M}_0'$, where $[-1]$ is the inversion morphism `negMor E.f E.L`. Then there exist a local Noetherian commutative ring $R_1$, a ring homomorphism $\varphi:R_1\to R$, a fake elliptic curve $E_1$ over $R_1$ for the same $\Lambda$ and $N$, and a morphism $g:E.A\to E_1.A$ making the square with $E.f$, $E_1.f$ and $\operatorname{Spec}\varphi$ cartesian, such that $\varphi$ is injective and local, and there are modules $\mathcal{M}_1,\mathcal{M}_1'$ on $E_1.A$ satisfying `IsCanonicalPolData` for $E_1$ and $\mathrm{star}$ with $g^*\mathcal{M}_1\cong\mathcal{M}$ and $g^*\mathcal{M}_1'\cong\mathcal{M}'$. The compatibility of $g$ with the group laws, the $\Lambda$-actions and the level structures is not part of the conclusion.
--
--   This is the spreading-out and localisation step for fake elliptic curves: it replaces an arbitrary local base $R$ by a local Noetherian base $R_1$ mapping injectively and locally into $R$, carrying along two canonical polarisation data whose pullbacks recover the original ones. It is used in the comparison of canonical polarisation data over a general local base with the Noetherian case, where uniqueness statements available over Noetherian local rings are transported back along $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNoetherianRing_injective_isLocalHom_isPullback_isCanonicalPol_nonempty_pullback_iso_of_locIsoOnBase_sqrt_of_isLocalRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (R : Type) [CommRing R] [IsLocalRing R] (E : FakeEllipticCurve Λ N R)
    (𝓜 𝓜' : E.A.Modules) (h : E.IsCanonicalPol star 𝓜) (h' : E.IsCanonicalPol star 𝓜')
    (𝓜₀ 𝓜₀' : E.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓜₀) (h₀' : Scheme.Modules.IsInvertible 𝓜₀')
    (hK₀ : KernelTrivial E.f E.L 𝓜₀) (hK₀' : KernelTrivial E.f E.L 𝓜₀')
    (hsq : LocIsoOnBase E.f 𝓜 (𝓜₀ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀))
    (hsq' : LocIsoOnBase E.f 𝓜' (𝓜₀' ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀')) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsLocalRing R₁) (_ : IsNoetherianRing R₁) (φ : R₁ →+* R)
      (E₁ : FakeEllipticCurve Λ N R₁) (g : E.A ⟶ E₁.A),
      CategoryTheory.IsPullback g E.f E₁.f (Spec.map (CommRingCat.ofHom φ)) ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      ∃ (𝓜₁ 𝓜₁' : E₁.A.Modules), E₁.IsCanonicalPol star 𝓜₁ ∧ E₁.IsCanonicalPol star 𝓜₁' ∧
        Nonempty ((Scheme.Modules.pullback g).obj 𝓜₁ ≅ 𝓜) ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜₁' ≅ 𝓜') := by sorry
