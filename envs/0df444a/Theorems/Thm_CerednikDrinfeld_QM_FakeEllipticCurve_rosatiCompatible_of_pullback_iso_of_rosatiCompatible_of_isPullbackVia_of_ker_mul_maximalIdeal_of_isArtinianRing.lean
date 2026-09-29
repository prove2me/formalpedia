-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/aefd176f-e2ba-5676-96ac-8a2d23d3fd3c
-- title:
--   Rosati compatibility lifts along small thickenings of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B_1$ be an Artinian local commutative ring and $B_0$ a commutative $B_1$-algebra such that the structure map $B_1 \to B_0$ is surjective, its kernel $K$ is a nilpotent ideal, and $K$ is annihilated by the maximal ideal, i.e. $xm = 0$ for all $x \in K$ and $m \in \mathfrak{m}_{B_1}$. Let $E$ be a fake elliptic curve of level data $(\Lambda, N)$ over $B_1$ and $E_0$ one over $B_0$, and let $g : E_0.A \to E.A$ satisfy `FakeEllipticCurve.IsPullbackVia` for the map $B_1 \to B_0$: $g$ makes $E_0.A$ the fibre product of $E.A$ with $\operatorname{Spec} B_0$, it carries the relative group law of $E_0$ to that of $E$ on points, it intertwines the $\Lambda$-actions ($E_0.\mathrm{act}(x) \circ g = g \circ E_0 \to E$, i.e. $E_0.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $E.\mathrm{act}(x)$), and points factoring through the level scheme of $E_0$ push forward to points factoring through that of $E$. Let $\star : \Lambda \to \Lambda$ be an arbitrary map, $\mathcal{L}_0$ a module on $E_0.A$, and $\mathcal{L}$ a module on $E.A$ that is invertible (every point of $E.A$ has a neighbourhood on which $\mathcal{L}$ restricts isomorphically to the unit), and assume the pullback of $\mathcal{L}$ along $g$ is isomorphic to $\mathcal{L}_0$. If $\mathcal{L}_0$ is Rosati-compatible through $\star$ for $E_0$, then so is $\mathcal{L}$ for $E$: for every $x \in \Lambda$, the pullbacks of the Mumford bundle $m^*\mathcal{L} \otimes (\mathrm{pr}_1^*\mathcal{L}^\vee \otimes \mathrm{pr}_2^*\mathcal{L}^\vee)$ on $E.A \times_{\operatorname{Spec} B_1} E.A$ along $(\mathrm{pr}_1, E.\mathrm{act}(x) \circ \mathrm{pr}_2)$ and along $(E.\mathrm{act}(x^\star) \circ \mathrm{pr}_1, \mathrm{pr}_2)$ become isomorphic over some open neighbourhood of each point of $\operatorname{Spec} B_1$.
--
--   This is the small-kernel (kernel killed by the maximal ideal) case of the statement that Rosati compatibility of an invertible module on a fake elliptic curve persists when the base is thickened infinitesimally. It is the inductive step cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing), where the general nilpotent-kernel case over an Artinian local base is obtained by $\mathfrak{m}$-adic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_ker_mul_maximalIdeal_of_isArtinianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (star : ↥Λ → ↥Λ)
    (𝓛₀ : E₀.A.Modules) (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀))
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
