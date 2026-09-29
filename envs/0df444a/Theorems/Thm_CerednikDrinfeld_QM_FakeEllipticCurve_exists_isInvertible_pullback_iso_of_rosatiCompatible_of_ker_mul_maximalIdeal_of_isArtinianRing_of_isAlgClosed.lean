-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isArtinianRing_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isArtinianRing_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/db3f14f8-0e91-5468-ba70-db3e80a11c03
-- title:
--   Lifting a Rosati-compatible invertible module along a small extension
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $N$ be a natural number and $p$ a prime with $p = q$ or $p = q'$. Let $B_1$ be an Artinian local ring with algebraically closed residue field in which the image of $p$ is nilpotent, and let $B_0$ be a $B_1$-algebra whose structure map is surjective and whose kernel $I$ satisfies $x m = 0$ for all $x \in I$ and all $m$ in the maximal ideal of $B_1$. Let $E$ be a fake elliptic curve with $\Lambda$-action and level $N$ over $B_1$, let $E_0$ be one over $B_0$, and let $g : E_0.A \to E.A$ exhibit $E_0$ as the base change of $E$ along $B_1 \to B_0$ in the sense of `IsPullbackVia`: $g$ makes $E_0.A$ a pullback of $E.A$ along $\operatorname{Spec} B_0 \to \operatorname{Spec} B_1$, is compatible with the relative group laws and with the $\Lambda$-actions, and sends points factoring through the level structure of $E_0$ to points factoring through that of $E$. Let $\mathcal{L}_0$ be an $\mathcal{O}$-module on $E_0.A$ that is invertible (every point has an open neighbourhood on which the restriction is isomorphic to the unit module) and Rosati-compatible through $\mathrm{star}$: for each $x \in \Lambda$, the pullbacks of the Mumford bundle $m^*\mathcal{L}_0 \otimes p_1^*\mathcal{L}_0^{\vee} \otimes p_2^*\mathcal{L}_0^{\vee}$ along $(\mathrm{id}, \mathrm{act}(x))$ and along $(\mathrm{act}(\mathrm{star}(x)), \mathrm{id})$ become isomorphic over the preimage of some open neighbourhood of each point of $\operatorname{Spec} B_0$. Then there exists an invertible $\mathcal{O}$-module $\mathcal{L}$ on $E.A$ together with an isomorphism $g^*\mathcal{L} \cong \mathcal{L}_0$. No Rosati compatibility is asserted for $\mathcal{L}$.
--
--   This is the square-zero (small surjection) step in lifting a Rosati-compatible invertible module, i.e. the vanishing of the obstruction class to deforming $\mathcal{L}_0$ across $B_1 \to B_0$, for fake elliptic curves at a prime dividing the discriminant of the quaternion algebra. It is the inductive step used by the two statements that lift an invertible module along a general surjection of Artinian local rings by iterating along the $\mathfrak{m}$-adic filtration of the kernel, Rosati compatibility of the lift being supplied separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isArtinianRing_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isArtinianRing_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁] [IsAlgClosed (ResidueField B₁)]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (hpB : IsNilpotent ((p : ℕ) : B₁))
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (𝓛₀ : E₀.A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) := by sorry
