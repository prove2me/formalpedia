-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3a07da24-9657-5bc0-a55f-12c1f802f259
-- title:
--   Rosati compatibility lifts along nilpotent thickenings of Artinian local base
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a natural number $N$. Let $B_1$ be a commutative local Artinian ring and $B_0$ a commutative $B_1$-algebra such that the structure map $B_1 \to B_0$ is surjective and its kernel is a nilpotent ideal. Let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $B_1$ and $E_0$ one over $B_0$, and let $g : E_0.A \to E.A$ satisfy `IsPullbackVia` for $B_1 \to B_0$: the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}$ of the structure map is a pullback, $g$ carries the relative group law of $E_0$ to that of $E$ on points, $g$ intertwines the two $\Lambda$-actions ($E_0.\mathrm{act}(x) \circ\!\!\to g = g \circ\!\!\to E.\mathrm{act}(x)$ in diagrammatic order), and points of $E_0$ factoring through its level scheme push forward to points factoring through that of $E$. Let $\mathrm{star} : \Lambda \to \Lambda$ be an arbitrary map, $\mathcal{L}_0$ a module on $E_0.A$ and $\mathcal{L}$ an invertible module on $E.A$ (locally isomorphic to the unit), together with some isomorphism $g^{*}\mathcal{L} \cong \mathcal{L}_0$. Assume $\mathcal{L}_0$ is Rosati compatible with respect to $\mathrm{star}$, i.e. for every $x \in \Lambda$ the pullbacks of the Mumford bundle $m^{*}\mathcal{L}_0 \otimes \mathrm{pr}_1^{*}\mathcal{L}_0^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal{L}_0^{\vee}$ along $(\mathrm{pr}_1, \mathrm{act}(x)\circ \mathrm{pr}_2)$ and along $(\mathrm{act}(\mathrm{star}\,x)\circ \mathrm{pr}_1, \mathrm{pr}_2)$ become isomorphic over a neighbourhood of each point of $\operatorname{Spec} B_0$. The conclusion is the same Rosati compatibility for $\mathcal{L}$, $E.\mathrm{act}$ and $\mathrm{star}$ over $\operatorname{Spec} B_1$.
--
--   This is the descent (or persistence) step for Rosati compatibility of an invertible module along a nilpotent thickening of an Artinian local base: compatibility of a polarising line bundle with the involution $\mathrm{star}$ on the quaternionic multiplications need only be checked after reduction. It feeds the construction of invertible modules that are simultaneously Rosati compatible and compatible with pullback over Artinian local rings, used in the deformation-theoretic study of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.rosatiCompatible_of_pullback_iso_of_rosatiCompatible_of_isPullbackVia_of_isArtinianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [IsArtinianRing B₁]
    [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B₁ B₀)))
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (star : ↥Λ → ↥Λ)
    (𝓛₀ : E₀.A.Modules) (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀))
    (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star) :
    RosatiCompatible E.f E.L 𝓛 E.act E.act_over star := by sorry
