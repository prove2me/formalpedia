-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_rosatiCompatible_of_isPullback_of_isDiscreteValuationRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isPullback_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/00eb0302-a721-5c11-afa5-ec87feb49db2
-- title:
--   Specialisation of a Rosati-compatible principal sheaf over a DVR
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be an order maximal among the orders containing it, $\mu \in \Lambda$ with $\mu^2 = -qq'$, and $\star : \Lambda \to \Lambda$ a map with $\mu\,\star(x) = \bar x\,\mu$ for all $x$. Let $N$ be a natural number, $R$ a discrete valuation domain with fraction field $KK$, $k$ an algebraically closed field and $\varphi : R \to k$ a surjective ring homomorphism. Let $E_R$, $E_K$, $E$ be fake elliptic curves for $(\Lambda, N)$ over $R$, $KK$, $k$ respectively, with $E_K$ and $E$ obtained from $E_R$ by base change in the sense of `FakeEllipticCurve.IsPullback`: there is a morphism of the total spaces forming a pullback square over the corresponding map of bases, compatible with the relative group laws and with the $\Lambda$-actions, and through which level-structure points factor. Suppose $\mathcal L_K$ is a module on $E_K.A$ which is invertible (locally isomorphic to the unit), satisfies `KernelTrivial` (any point of $E_K$ over any affine base whose slice of the Mumford bundle $m^*\mathcal L_K \otimes p_1^*\mathcal L_K^{\vee} \otimes p_2^*\mathcal L_K^{\vee}$ is locally trivial on the base is the identity section), has strictly positive geometric fibre $h^0$ over every algebraically closed field receiving $KK$, and is `RosatiCompatible` for $\star$ (for each $b \in \Lambda$ the pullbacks of the Mumford bundle along $(\mathrm{id}, \mathrm{act}\,b)$ and along $(\mathrm{act}\,\star b, \mathrm{id})$ are locally isomorphic over the base). Then there exists a module $\mathcal L_0$ on $E.A$ with the same four properties over $k$.
--
--   This is the specialisation step in the construction of a principal, Rosati-compatible polarisation on a fake elliptic curve: a sheaf with trivial Mumford kernel, positive fibre cohomology and compatibility with the Rosati-type involution descends from the generic fibre to the closed fibre of a model over a discrete valuation ring. It is used in the construction of such a sheaf over an algebraically closed field in which $2$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_rosatiCompatible_of_isPullback_of_isDiscreteValuationRing.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isPullback_of_isDiscreteValuationRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    (k : Type) [Field k] [IsAlgClosed k] (φ : R →+* k) (hφ : Function.Surjective φ)
    (E_R : FakeEllipticCurve Λ N R) (E_K : FakeEllipticCurve Λ N KK) (E : FakeEllipticCurve Λ N k)
    (hK : FakeEllipticCurve.IsPullback (algebraMap R KK) E_R E_K) (hk : FakeEllipticCurve.IsPullback φ E_R E)
    (𝓛K : E_K.A.Modules) (h𝓛K : (Scheme.Modules.IsInvertible 𝓛K ∧ KernelTrivial E_K.f E_K.L 𝓛K ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : KK →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E_K.f 𝓛K k' sk) ∧
      RosatiCompatible E_K.f E_K.L 𝓛K E_K.act E_K.act_over star)) :
    ∃ 𝓛₀ : E.A.Modules, (Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial E.f E.L 𝓛₀ ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E.f 𝓛₀ k' sk) ∧
      RosatiCompatible E.f E.L 𝓛₀ E.act E.act_over star) := by sorry
