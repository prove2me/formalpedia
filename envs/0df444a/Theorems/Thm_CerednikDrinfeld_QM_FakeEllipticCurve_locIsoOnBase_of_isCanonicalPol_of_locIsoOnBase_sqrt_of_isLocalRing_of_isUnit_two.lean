-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_locIsoOnBase_sqrt_of_isLocalRing_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_locIsoOnBase_sqrt_of_isLocalRing_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8929db8f-9af4-5be1-a5ae-6e84bf706a69
-- title:
--   Uniqueness of canonical polarisation data over a local base
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a > 0$ or $b > 0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order containing no larger order), $\mu \in \Lambda$ with $\mu^2 = -(qq') \cdot 1$, and $star : \Lambda \to \Lambda$ a map satisfying $\mu \cdot star(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $N \in \mathbb{N}$, let $R$ be a local commutative ring in which $2$ is a unit, and let $E$ be a `FakeEllipticCurve Λ N R`: an abelian scheme $f : A \to \operatorname{Spec} R$ of relative dimension $2$ with commutative relative group law $L$, a $\Lambda$-action by $f$-morphisms with the stated additivity, multiplicativity and trace conditions, and the further data recorded in that structure. Let $\mathcal{M}, \mathcal{M}'$ be modules on $A$ each satisfying `E.IsCanonicalPol star`, i.e. `IsCanonicalPolData` for $E.f$, $E.L$, the $\Lambda$-action and $star$. Let $\mathcal{M}_0, \mathcal{M}_0'$ be invertible modules on $A$ (Zariski-locally isomorphic to the unit module) which are `KernelTrivial` for $E.f$, $E.L$: for every commutative ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} R$ and every section $x$ of $f$ over $t$, if the pullback along the slice $\operatorname{sliceAt} x$ of the Mumford bundle of the relevant sheaf is isomorphic to the unit module locally on $\operatorname{Spec} R'$, then $x$ is the identity section. Assume finally that $\mathcal{M}$ and $\mathcal{M}'$ are, locally on the base, isomorphic to $\mathcal{M}_0 \otimes [-1]^{*}\mathcal{M}_0$ and $\mathcal{M}_0' \otimes [-1]^{*}\mathcal{M}_0'$ respectively, where $[-1]$ is the inversion morphism of $L$. Then $\mathcal{M}$ and $\mathcal{M}'$ are `LocIsoOnBase` for $E.f$: every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over which the pullbacks of $\mathcal{M}$ and $\mathcal{M}'$ to $f^{-1}(U)$ are isomorphic.
--
--   This is the uniqueness, up to local isomorphism on the base, of the canonical polarisation datum on a fake elliptic curve over a local base, under the extra assumption that both data already admit principal square roots over that base. It feeds the corresponding uniqueness statement over an arbitrary local base in which $2$ is invertible, used in the construction of the Shimura curve moduli problem underlying the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_locIsoOnBase_sqrt_of_isLocalRing_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_locIsoOnBase_sqrt_of_isLocalRing_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (R : Type) [CommRing R] (h2 : IsUnit (2 : R)) [IsLocalRing R] (E : FakeEllipticCurve Λ N R)
    (𝓜 𝓜' : E.A.Modules) (h : E.IsCanonicalPol star 𝓜) (h' : E.IsCanonicalPol star 𝓜')
    (𝓜₀ 𝓜₀' : E.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓜₀) (h₀' : Scheme.Modules.IsInvertible 𝓜₀')
    (hK₀ : KernelTrivial E.f E.L 𝓜₀) (hK₀' : KernelTrivial E.f E.L 𝓜₀')
    (hsq : LocIsoOnBase E.f 𝓜 (𝓜₀ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀))
    (hsq' : LocIsoOnBase E.f 𝓜' (𝓜₀' ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓜₀')) :
    LocIsoOnBase E.f 𝓜 𝓜' := by sorry
