-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/6a0fc877-5666-519b-b4de-b77b18ab3032
-- title:
--   Uniqueness of symmetrised principal Rosati-compatible bundles on fake elliptic curves
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subset \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\operatorname{star} : \Lambda \to \Lambda$ satisfy $\mu\,\operatorname{star}(x) = \bar x\,\mu$ for all $x \in \Lambda$. Let $N$ be a natural number, $k$ an algebraically closed field, and $E$ a `FakeEllipticCurve` for $\Lambda$, $N$ over $k$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, and an action $E.act$ of $\Lambda$ by morphisms over the base, together with its further data. Let $\mathcal L_0, \mathcal L_1$ be modules on $E.A$ which are invertible (locally isomorphic to the unit module), each with trivial kernel group scheme in the sense of `KernelTrivial` (for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every section $x$ of $E.f$ over $t$, if the pullback of the Mumford bundle of $\mathcal L_i$ along the slice at $x$ is locally on the base isomorphic to the unit module, then $x$ is the identity section), each with strictly positive geometric-fibre $h^0$ rank `geomFibreH0Finrank` after every base change to an algebraically closed field $k'$ along a ring homomorphism $k \to k'$, and each `RosatiCompatible` with the $\Lambda$-action and the involution $\operatorname{star}$, meaning that for every $m \in \Lambda$ the pullbacks of the Mumford bundle along $(\mathrm{pr}_1, \mathrm{pr}_2 \circ E.act\,m)$ and along $(E.act(\operatorname{star} m) \circ \mathrm{pr}_1, \mathrm{pr}_2)$ are locally isomorphic over the base. Then $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ and $\mathcal L_1 \otimes [-1]^{*}\mathcal L_1$ satisfy `LocIsoOnBase` for $E.f$, where $[-1]$ is the morphism `negMor` inverting the identity section for $E.L$: there is an open neighbourhood of each point of $\operatorname{Spec} k$ over whose preimage the two modules become isomorphic.
--
--   This is the uniqueness statement for the symmetrisation $\mathcal L \otimes [-1]^{*}\mathcal L$ of a principal, positive, Rosati-compatible line bundle on a fake elliptic curve over an algebraically closed field of arbitrary characteristic, the classical input being Mumford's theory of $\varphi_{\mathcal L}$, $K(\mathcal L)$ and the Rosati involution. It serves as the fibrewise ingredient for [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed), which compares canonical polarisations in the quaternionic moduli problem underlying the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_tensor_pullback_negMor_of_kernelTrivial_of_rosatiCompatible_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (𝓛₀ 𝓛₁ : E.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (h₁ : Scheme.Modules.IsInvertible 𝓛₁)
    (hK₀ : KernelTrivial E.f E.L 𝓛₀) (hK₁ : KernelTrivial E.f E.L 𝓛₁)
    (hpos₀ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E.f 𝓛₀ k' sk)
    (hpos₁ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E.f 𝓛₁ k' sk)
    (hR₀ : RosatiCompatible E.f E.L 𝓛₀ E.act E.act_over star) (hR₁ : RosatiCompatible E.f E.L 𝓛₁ E.act E.act_over star) :
    LocIsoOnBase E.f (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓛₀)
      (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor E.f E.L)).obj 𝓛₁) := by sorry
