-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_gradNorm_le_near_boundary
-- name    : FiniteEnergyPlane.exists_gradNorm_le_near_boundary
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:37:39.284128+00:00
-- url     : https://prove2.me/theorems/fb6fb450-5647-4bc7-b7c8-16b8d3065211
-- title:
--   Gradient bound near the boundary
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Let $K\subset D\setminus\{z_0\}$ be compact and let $q_1,q_2,q_3$ be distinct points of the unit circle. Then there are $\varepsilon>0$ and $M$ such that every embedded $\tilde J$-holomorphic disk $u$ whose boundary loop $t\mapsto e(c(t))$ lies in $e(K)$, has winding number $1$ around $e(z_0)$, and has $c(0),c(\tfrac14),c(\tfrac12)$ on the characteristic leaves through $q_1,q_2,q_3$ satisfies
--   $$|\nabla u(z)|\le M\qquad\text{for }1-\varepsilon<|z|<1 .$$
--
--   Here $D$ is the closed unit disk. The set $K$ may meet the unit circle, so the bound is uniform for loops close to the orbit. The three leaves fix the parametrization of the disk.
--
--   **Formalization Note** $|\nabla u|$ is `gradNorm`, the norm of the derivative of the pair ($\mathbb{R}$-coordinate, projection to $S$). The source is stated for a compact annulus foliated by leaves joining its boundary circles. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), 159–226, Theorem 2.1

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1995), Theorem 2.1. Let `e` be a special spanning disk, let `K` be a compact set
of parameters in the closed unit disk not containing `z₀`, and let `q₁, q₂, q₃` be three distinct points of the
unit circle. There are `ε > 0` and `M` such that every embedded `J̃`-holomorphic disk `u` whose boundary loop
`t ↦ e(c(t))` lies in `e(K)`, winds once around `e z₀`, and meets the characteristic leaves through
`q₁, q₂, q₃` at `1, i, -1` satisfies `|∇u| ≤ M` for `1 - ε < |z| < 1`. -/
theorem exists_gradNorm_le_near_boundary (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (K : Set ℂ) (hK : IsCompact K) (hK₁ : K ⊆ closedBall 0 1) (hK₀ : z₀ ∉ K)
    (q₁ q₂ q₃ : ℂ) (hq₁ : q₁ ∈ sphere (0 : ℂ) 1) (hq₂ : q₂ ∈ sphere (0 : ℂ) 1)
    (hq₃ : q₃ ∈ sphere (0 : ℂ) 1) (h₁₂ : q₁ ≠ q₂) (h₂₃ : q₂ ≠ q₃) (h₁₃ : q₁ ≠ q₃) :
    ∃ ε > 0, ∃ M : ℝ, ∀ (u : ℂ → V 1) (c : ℝ → ℂ), IsEmbeddedHoloDisk H J e z₀ K u →
      HasDiskBoundary e z₀ K u c → SameLeaf e (c 0) q₁ → SameLeaf e (c (1 / 4)) q₂ →
      SameLeaf e (c (1 / 2)) q₃ →
      ∀ z : ℂ, 1 - ε < ‖z‖ → ‖z‖ < 1 → gradNorm H u z ≤ M := by
  sorry

end FiniteEnergyPlane
