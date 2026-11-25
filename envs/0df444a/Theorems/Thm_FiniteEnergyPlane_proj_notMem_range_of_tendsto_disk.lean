-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_notMem_range_of_tendsto_disk
-- name    : FiniteEnergyPlane.proj_notMem_range_of_tendsto_disk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:38:26.085042+00:00
-- url     : https://prove2.me/theorems/cd803f4c-da08-4197-99c2-cff645f43a7a
-- title:
--   A limit of disks disjoint from the cylinder over the orbit is disjoint from it
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Let $u_n$ be embedded $\tilde J$-holomorphic disks with boundary loop in $e(\mathring D)$, disjoint from $\mathbb{R}\times x(\mathbb{R})$, and let $u$ be an embedded $\tilde J$-holomorphic disk with boundary loop in $e(D)$, all boundary loops having winding number $1$ around $e(z_0)$. If $u_n\to u$ in $C^\infty(D)$, then
--   $$u(D)\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset .$$
--
--   $D$ is the closed unit disk and $\mathring D$ the open one. In particular the boundary loop of $u$ does not touch $x(\mathbb{R})$, and lies in $e(\mathring D)$ again.
--
--   **Formalization Note** A point $y\ne0$ lies on $\mathbb{R}\times x(\mathbb{R})$ if $\mathrm{proj}(y)\in x(\mathbb{R})$. The source has a one-parameter family of disks; only a convergent sequence is needed to state the conclusion. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), 159–226, Theorem 4.4; H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, Proposition 3.2 (iii)

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1995), Theorem 4.4; Hofer–Wysocki–Zehnder (1999, tight 3-sphere II), Proposition 3.2
(iii). Let `e` be a special spanning disk for the prime orbit `P`. If embedded `J̃`-holomorphic disks `u_n` with
boundary in the interior of `e`, disjoint from `ℝ × x(ℝ)`, converge in `C^∞` on the closed disk to an embedded
`J̃`-holomorphic disk `u` with boundary on `e` (possibly meeting `x(ℝ)`), all winding once around `e z₀`, then
`u` is disjoint from `ℝ × x(ℝ)`. -/
theorem proj_notMem_range_of_tendsto_disk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (u : ℂ → V 1) (hu : IsEmbeddedHoloDisk H J e z₀ (closedBall 0 1) u)
    (un : ℕ → ℂ → V 1) (hun : ∀ n, IsEmbeddedHoloDisk H J e z₀ (ball 0 1) (un n))
    (hdis : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1, proj H (un n z) ∉ Set.range P.x)
    (hconv : TendstoCInftyLocWithin un u (closedBall 0 1) ∅) :
    ∀ z ∈ closedBall (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x := by
  sorry

end FiniteEnergyPlane
