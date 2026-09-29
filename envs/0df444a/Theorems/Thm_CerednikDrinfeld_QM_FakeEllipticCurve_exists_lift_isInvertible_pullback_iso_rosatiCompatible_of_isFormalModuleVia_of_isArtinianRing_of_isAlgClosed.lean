-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_isInvertible_pullback_iso_rosatiCompatible_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_isInvertible_pullback_iso_rosatiCompatible_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8399ac11-6df1-566f-aa85-545f11834609
-- title:
--   Rosati-compatible Serre–Tate lifting of fake elliptic curves
-- statement:
--   Fix distinct primes $q \ne q'$ and $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated) maximal among orders above it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\operatorname{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \operatorname{star}(x) = \bar{x} \mu$. Let $N \in \mathbb{N}$, let $p$ be a prime equal to $q$ or $q'$, let $\mathrm{coord} : \Lambda \to \mathbb{Z}_{p^2} \times \mathbb{Z}_{p^2}$ satisfy `IsOrderCoord` (additive, $1 \mapsto (1,0)$, Frobenius-twisted multiplicativity with $p$ in the first coordinate, injective, $p$-adically dense image, and reduced-trace compatible), and assume $1 \in \Lambda$. Let $B_1$ be an Artinian local ring with algebraically closed residue field, $B_0$ a $B_1$-algebra with surjective structure map whose kernel is nilpotent, with $p$ nilpotent and $N$ invertible in $B_1$. Given a fake elliptic curve $E_0$ over $B_0$ with $\Lambda$-action and level structure, a formal $\mathcal{O}_D$-module $X$ over $B_1$ (a commutative two-dimensional formal group with $\mathbb{Z}_{p^2}$-action and uniformiser series $\varpi$ with $\varpi \circ \varpi = [p]$, $\varpi \circ [\alpha] = [\alpha^{\sigma}] \circ \varpi$), formal coordinates $\theta_0$ for $E_0.f$ exhibiting $X \otimes_{B_1} B_0$ as the formal module of $E_0$ via $\mathrm{coord}$, and an invertible module $\mathcal{L}_0$ on $E_0.A$ which is Rosati-compatible with the $\Lambda$-action through $\operatorname{star}$ (the two pullbacks of the Mumford bundle along $(1,\mathrm{act}\,x)$ and $(\mathrm{act}(\operatorname{star} x),1)$ are isomorphic locally on the base), the conclusion asserts the existence of a fake elliptic curve $E$ over $B_1$, a morphism $g : E_0.A \to E.A$ and formal coordinates $\theta$ for $E.f$ such that $g$ exhibits $E_0$ as the pullback of $E$ along $B_1 \to B_0$ (a pullback square compatible with the group laws, intertwining the $\Lambda$-actions, and carrying level points to level points), $\theta$ exhibits $X$ as the formal module of $E$ via $\mathrm{coord}$, $\theta_0(B'',s)$ followed by $g$ equals $\theta(B'',s)$ for every $B''$ which is an algebra over both $B_1$ and $B_0$ compatibly and every tuple $s$ of nilpotents, and moreover there is an invertible module $\mathcal{L}$ on $E.A$ with $g^{*}\mathcal{L} \cong \mathcal{L}_0$ which is again Rosati-compatible through $\operatorname{star}$.
--
--   This is the polarised form of Serre–Tate lifting for fake elliptic curves over an Artin local base in which the residue characteristic $p$ divides the discriminant $qq'$: the curve, its $\Lambda$-action, its formal $\mathcal{O}_D$-module and a Rosati-compatible line bundle all lift together along a surjection with nilpotent kernel. It feeds the construction of towers of such lifts used in the Čerednik–Drinfeld uniformisation of the Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_isInvertible_pullback_iso_rosatiCompatible_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_isInvertible_pullback_iso_rosatiCompatible_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (coord : ↥Λ → Zp2 p × Zp2 p) (hcoord : IsOrderCoord Λ p coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁] [IsAlgClosed (ResidueField B₁)]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (hpB : IsNilpotent ((p : ℕ) : B₁)) (hN : IsUnit ((N : ℕ) : B₁))
    (E₀ : FakeEllipticCurve Λ N B₀) (X : FormalODModule p B₁) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (h₀ : E₀.IsFormalModuleVia coord (X.map (algebraMap B₁ B₀)) θ₀)

    (𝓛₀ : E₀.A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    ∃ (E : FakeEllipticCurve Λ N B₁) (g : E₀.A ⟶ E.A) (θ : RelativeGroupLaw.FormalCoordinates E.f 2),
      FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g ∧
      E.IsFormalModuleVia coord X θ ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B₁ B''] [Algebra B₀ B''] [IsScalarTower B₁ B₀ B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θ₀ B'' s).1 ≫ g = (θ B'' s).1) ∧
      ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
        Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) ∧
        RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
