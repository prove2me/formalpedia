-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_rosatiCompatible_of_isPullbackVia_of_isArtinianRing_of_isAlgClosed_residueField_of_isUnit_two_of_charP_residueField
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_rosatiCompatible_of_isPullbackVia_of_isArtinianRing_of_isAlgClosed_residueField_of_isUnit_two_of_charP_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/920b684d-607e-5887-b089-e2ac0dc6310b
-- title:
--   Rosati-compatible invertible sheaf lifts along nilpotent thickenings
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $\mu \in \Lambda$ with $\mu^2 = -(qq')\cdot 1$, and $\star : \Lambda \to \Lambda$ a map with $\mu\,\star(x) = \bar{x}\,\mu$ for all $x \in \Lambda$; fix a level $N$. Let $B_1$ be a commutative Artinian local ring with algebraically closed residue field in which $2$ is a unit, of residue characteristic a prime $p$, and let $B_0$ be a $B_1$-algebra whose structure map is surjective with nilpotent kernel. Let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $B_1$, $E_0$ one over $B_0$, and $g : E_0.A \to E.A$ exhibiting $E_0$ as the base change of $E$ along $B_1 \to B_0$ in the sense of `IsPullbackVia`: the square formed by $g$, the structure morphisms and $\mathrm{Spec}$ of $B_1 \to B_0$ is a pullback, $g$ carries the relative group law of $E_0$ to that of $E$ on points, commutes with the $\Lambda$-actions, and points factoring through the level structure of $E_0$ have their images factoring through that of $E$. Let $\mathcal{L}_0$ be an invertible module on $E_0.A$ (locally on $E_0.A$ pullback-isomorphic to the unit) which is Rosati-compatible for $\star$: for each $x \in \Lambda$, the pullbacks of the Mumford bundle $m^*\mathcal{L}_0 \otimes \mathrm{pr}_1^*\mathcal{L}_0^{\vee} \otimes \mathrm{pr}_2^*\mathcal{L}_0^{\vee}$ along $(\mathrm{pr}_1, \mathrm{act}(x)\circ\mathrm{pr}_2)$ and along $(\mathrm{act}(\star x)\circ\mathrm{pr}_1, \mathrm{pr}_2)$ become isomorphic over the preimage of some open neighbourhood of each point of $\mathrm{Spec}\,B_0$. The conclusion is that there exists an invertible module $\mathcal{L}$ on $E.A$ with $g^*\mathcal{L} \cong \mathcal{L}_0$ and with $\mathcal{L}$ Rosati-compatible for $E$ in the same sense.
--
--   This is the statement that a polarisation datum compatible with the involution $\star$ (the Rosati involution attached to $\mu$) rides along an arbitrary $\Lambda$-equivariant nilpotent thickening of a fake elliptic curve, with no restriction on the residue characteristic beyond its being odd. It feeds the construction of Rosati-compatible invertible sheaves on versal deformation towers and the assembly of canonical polarisation data for fake elliptic curves in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_rosatiCompatible_of_isPullbackVia_of_isArtinianRing_of_isAlgClosed_residueField_of_isUnit_two_of_charP_residueField.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_rosatiCompatible_of_isPullbackVia_of_isArtinianRing_of_isAlgClosed_residueField_of_isUnit_two_of_charP_residueField
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁] [IsAlgClosed (ResidueField B₁)]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (h2 : IsUnit (2 : B₁))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField B₁) p]
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (𝓛₀ : E₀.A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) ∧
      RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
