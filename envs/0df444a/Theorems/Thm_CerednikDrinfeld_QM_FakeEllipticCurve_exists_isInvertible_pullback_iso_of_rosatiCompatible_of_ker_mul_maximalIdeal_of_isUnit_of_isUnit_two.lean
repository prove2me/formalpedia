-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isUnit_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isUnit_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/6b4ff9ea-c6c0-596d-b733-ac7e67d10d4d
-- title:
--   Descent of invertible modules along small extensions away from 2qq'
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ divides $q$ or $q'$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N$ be a natural number and $p$ a prime. Let $B_1$ be an Artinian local ring with algebraically closed residue field and $B_0$ a $B_1$-algebra with surjective structure map whose kernel annihilates $\mathfrak{m}_{B_1}$ (a small extension), and assume $p$ is nilpotent in $B_1$ while $qq'$ and $2$ are units in $B_1$. Let $E$ be a fake elliptic curve of level $N$ over $B_1$ (an abelian scheme with commutative relative group law, all fibres of Krull dimension $2$, a $\Lambda$-action by base-preserving endomorphisms subject to the additivity, multiplicativity and trace conditions, together with the level datum) and $E_0$ one over $B_0$, and let $g:E_0.A\to E.A$ exhibit $E_0$ as the pullback of $E$ along $B_1\to B_0$: the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}$ of the structure map is cartesian, $g$ is compatible with the group laws, intertwines the two $\Lambda$-actions, and level-structure points of $E_0$ lift through $E.\mathrm{lev}$. Finally let $\mathcal{L}_0$ be an invertible module on $E_0.A$ (each point has a neighbourhood on which it becomes isomorphic to the unit module) which is Rosati-compatible for $E_0$ and $\mathrm{star}$: for each $x\in\Lambda$, the pullbacks of the Mumford bundle $m^*\mathcal{L}_0\otimes p_1^*\mathcal{L}_0^{\vee}\otimes p_2^*\mathcal{L}_0^{\vee}$ along $(\mathrm{id},\mathrm{act}(x))$ and along $(\mathrm{act}(\mathrm{star}\,x),\mathrm{id})$ are isomorphic locally over $\operatorname{Spec}B_0$. Then there is an invertible module $\mathcal{L}$ on $E.A$ with $g^*\mathcal{L}\cong\mathcal{L}_0$. The conclusion asserts only invertibility of $\mathcal{L}$ and the isomorphism after pullback; no Rosati compatibility of $\mathcal{L}$ is claimed.
--
--   This is the vanishing of the Picard obstruction to deforming a Rosati-compatible line bundle on a fake elliptic curve along a small extension of Artinian local rings, in the case where the residue characteristic is coprime to $2qq'$, the quaternion algebra being split at the residue characteristic. It is the split counterpart of the corresponding statement at the primes dividing the discriminant, and feeds the step-by-step deformation of a polarisation along the $\mathfrak{m}$-adic filtration used in the moduli-theoretic side of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isUnit_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_rosatiCompatible_of_ker_mul_maximalIdeal_of_isUnit_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime]
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁] [IsAlgClosed (ResidueField B₁)]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (hpB : IsNilpotent ((p : ℕ) : B₁)) (hqq : IsUnit ((q * q' : ℕ) : B₁)) (h2 : IsUnit (2 : B₁))
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (𝓛₀ : E₀.A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) := by sorry
