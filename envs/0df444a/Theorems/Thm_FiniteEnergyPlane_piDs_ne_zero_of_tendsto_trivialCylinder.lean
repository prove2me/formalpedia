-- Prove2me | Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_tendsto_trivialCylinder
-- name    : FiniteEnergyPlane.piDs_ne_zero_of_tendsto_trivialCylinder
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:40:01.028366+00:00
-- url     : https://prove2.me/theorems/84421442-b7f3-4869-b785-fb0dc0db9d1f
-- title:
--   Disks close to the trivial half-cylinder have nowhere vanishing $\xi$-derivative
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Let $u_n$ be $\tilde J$-holomorphic disks without punctures, with boundary loop in $e(\mathring D)$ of winding number $1$ around $e(z_0)$, converging in $C^\infty_{loc}(D\setminus\{0\})$, up to the boundary of $D$, to the trivial cylinder $F_P(e^{2\pi(s+it)})=(Ts,x(Tt))$. Then for all large $n$
--   $$\pi\cdot\partial_s(\mathrm{proj}\circ u_n)(z)\ne0\qquad\text{for all }z\in\mathring D ,$$
--   where $\pi:TS\to\xi$ is the projection along $R$.
--
--   $D$ is the closed unit disk and $\mathring D$ the open one. In particular the projections of these disks to $S$ are immersions transverse to the Reeb field.
--
--   **Formalization Note** The left-hand side is `piDs`, in the coordinates of the global frame of $\xi$. The disks are not assumed to be embedded. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Lemma 3.9; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 5.9

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Lemma 3.9; Hryniewicz (2012), Lemma 5.9. Let `e` be a special spanning disk for `P`, and let
`u_n` be `J̃`-holomorphic disks with boundary in the interior of `e`, winding once around `e z₀`, that converge in
`C^∞_loc` on the closed disk minus `0` to the trivial cylinder over `P`. For all large `n`, the `ξ`-component of
the derivative of `u_n` vanishes nowhere in the open disk. -/
theorem piDs_ne_zero_of_tendsto_trivialCylinder (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (u : ℕ → ℂ → V 1) (hu : ∀ n, IsDiskCurve H J e z₀ (ball 0 1) ∅ (u n))
    (hconv : TendstoCInftyLocWithin u (trivialCylinder P) (closedBall 0 1) {0}) :
    ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) 1, piDs H (u n) z ≠ 0 := by
  sorry

end FiniteEnergyPlane
