-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9304a945-c6cf-5438-b687-2b35c2430317
-- title:
--   Rosati-compatible principal bundle on a fake elliptic curve
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\star : \Lambda \to \Lambda$ be any map with $\mu\,(x^{\star}) = \bar{x}\,\mu$ for all $x \in \Lambda$. Let $N$ be a natural number, $k$ an algebraically closed field in which $2$ is a unit, and $E$ a `FakeEllipticCurve Λ N k`: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, and an action $E.act$ of $\Lambda$ by endomorphisms over the base satisfying the additivity, multiplicativity, trace and level-$N$ conditions of that structure. Then there exists an $\mathcal{O}_{E.A}$-module $\mathcal{L}_0$ which is invertible (locally around each point of $E.A$ isomorphic, after restriction, to the unit module), such that: (i) `KernelTrivial E.f E.L` $\mathcal{L}_0$ holds, that is, for every commutative ring $R$, every morphism $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x$ of $E.A$ over $t$, if the pullback along the slice of $x$ of the Mumford bundle $m^{*}\mathcal{L}_0 \otimes p_1^{*}\mathcal{L}_0^{\vee} \otimes p_2^{*}\mathcal{L}_0^{\vee}$ is, locally on the base, isomorphic to the unit module, then $x$ is the identity section $E.L.one\,t$; (ii) for every algebraically closed field $k'$ and every ring homomorphism $k \to k'$, the geometric fibre invariant `Scheme.Modules.geomFibreH0Finrank E.f` $\mathcal{L}_0\,k'$ — the $k'$-dimension of the global sections of the pullback of $\mathcal{L}_0$ to the corresponding fibre — is strictly positive; and (iii) `RosatiCompatible` holds for $\mathcal{L}_0$, $E.act$ and $\star$: for each $\beta \in \Lambda$ the pullbacks of the Mumford bundle along $(p_1, E.act\,\beta \circ p_2)$ and along $(E.act\,(\beta^{\star}) \circ p_1, p_2)$ are isomorphic locally on the base.
--
--   This is the existence, over an algebraically closed field in which $2$ is invertible, of a principal polarisation datum on a fake elliptic curve with $\Lambda$-action whose Rosati involution induces the given involution $\star = \mu^{-1}\bar{\;}\,\mu$ on $\Lambda$. It is the consumer-facing form of the construction, obtained from the characteristic-zero case by lifting along a complete discrete valuation ring, and it feeds the assembly of canonical polarisation data for the quaternionic moduli problem underlying the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_isUnit_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (h2 : IsUnit (2 : k)) (E : FakeEllipticCurve Λ N k) :
    ∃ 𝓛₀ : E.A.Modules, Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial E.f E.L 𝓛₀ ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank E.f 𝓛₀ k' sk) ∧
      RosatiCompatible E.f E.L 𝓛₀ E.act E.act_over star := by sorry
