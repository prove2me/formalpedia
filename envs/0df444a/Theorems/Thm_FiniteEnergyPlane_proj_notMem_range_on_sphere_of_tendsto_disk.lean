-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_notMem_range_on_sphere_of_tendsto_disk
-- name    : FiniteEnergyPlane.proj_notMem_range_on_sphere_of_tendsto_disk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T22:28:07.581023+00:00
-- url     : https://prove2.me/theorems/9f812299-b54f-462f-8095-b5304241c050
-- title:
--   Limits of disks disjoint from the trivial cylinder: the boundary circle
-- statement:
--   Let $S = H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with compatible $J$, let $P = (x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Let $u_n$ be embedded $\tilde J$-holomorphic disks with boundary loop in $e$ of the open unit disk, winding once around $e(z_0)$ and disjoint from $\mathbb{R}\times x(\mathbb{R})$ on the closed disk, converging in $C^\infty$ on the closed unit disk to an embedded $\tilde J$-holomorphic disk $u$ whose boundary loop lies in $e$ of the closed unit disk and winds once around $e(z_0)$. Then $u$ maps the unit circle into the complement of $\mathbb{R}\times x(\mathbb{R})$: $\mathrm{proj}\,u(z)\notin x(\mathbb{R})$ for $|z| = 1$.
--
--   Role: the boundary part of the statement that such limits stay disjoint from $\mathbb{R}\times x(\mathbb{R})$ (HWZ 1995, Theorem 4.4), the interior part being the statement that limits of curves missing a trivial cylinder miss it or lie in it.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), Theorem 4.4; H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998); U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 3

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1995), Theorem 4.4, at the boundary. Let `e` be a special spanning disk for the prime
orbit `P`. If embedded `J̃`-holomorphic disks `u_n` with boundary in the interior of `e`, disjoint from
`ℝ × x(ℝ)`, converge in `C^∞` on the closed disk to an embedded `J̃`-holomorphic disk `u` with boundary on `e`, all
winding once around `e z₀`, then `u` maps the unit circle into the complement of `ℝ × x(ℝ)`. -/
theorem proj_notMem_range_on_sphere_of_tendsto_disk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (u : ℂ → V 1) (hu : IsEmbeddedHoloDisk H J e z₀ (closedBall 0 1) u)
    (un : ℕ → ℂ → V 1) (hun : ∀ n, IsEmbeddedHoloDisk H J e z₀ (ball 0 1) (un n))
    (hdis : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1, proj H (un n z) ∉ Set.range P.x)
    (hconv : TendstoCInftyLocWithin un u (closedBall 0 1) ∅) :
    ∀ z ∈ sphere (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x := by
  sorry

end FiniteEnergyPlane
