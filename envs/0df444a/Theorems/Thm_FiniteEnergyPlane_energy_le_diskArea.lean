-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_le_diskArea
-- name    : FiniteEnergyPlane.energy_le_diskArea
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T20:36:28.085385+00:00
-- url     : https://prove2.me/theorems/784eedfc-412b-4469-ba9f-fff96fdc46d8
-- title:
--   The Hofer energy of a disk is at most the area of the spanning disk
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Let $u$ be a punctured $\tilde J$-holomorphic disk with punctures $\Gamma$, with boundary loop in $e(D)$ of winding number $1$ around $e(z_0)$, and whose $\mathbb{R}$-coordinate tends to $-\infty$ at every puncture. Then
--   $$E(u)\le\int_{\mathring D}\max\big(\omega_0(\partial_se,\partial_te),0\big)\,ds\,dt .$$
--
--   Here $E$ is Hofer's energy and $D$ is the closed unit disk and $\mathring D$ the open one. The bound is uniform over all such disks and all compatible $J$, and bounds the periods of the orbits at the punctures.
--
--   **Formalization Note** The right-hand side is `diskArea e`, the positive part of the $d\lambda_0$-area, which is at least the area itself. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.2; H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), 159–226, formulas (26) and (27)

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), § 3.2 (the energy estimate `E ≤ area(D)`); Hofer–Wysocki–Zehnder (1995), (26)–(27). Let
`e` be a special spanning disk. A punctured `J̃`-holomorphic disk with boundary on `e`, with `a → -∞` at every
puncture, has Hofer energy at most the positive part of the `dλ₀`-area of `e`. -/
theorem energy_le_diskArea (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ diskArea e := by
  sorry

end FiniteEnergyPlane
