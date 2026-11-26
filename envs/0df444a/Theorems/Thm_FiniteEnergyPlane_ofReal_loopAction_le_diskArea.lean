-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ofReal_loopAction_le_diskArea
-- name    : FiniteEnergyPlane.ofReal_loopAction_le_diskArea
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T19:47:54.870121+00:00
-- url     : https://prove2.me/theorems/09498c41-8684-571a-8426-595c16fe7838
-- title:
--   Boundary action of a pseudoholomorphic disk with boundary on a special spanning disk is bounded by the disk area
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on the symplectization. Let $e$ be a special spanning disk for the periodic Reeb orbit $P$ with singular point $e(z_0)$. Let $\Gamma$ be a finite subset of the open unit disk $D$, and let $u$ be a finite-energy $\tilde J$-holomorphic disk on $\bar D \setminus \Gamma$ whose boundary loop is $t \mapsto e(c(t))$ for a loop $c$ in the closed unit disk winding once around $z_0$, with $\mathrm{aCoord}(u(w)) \to -\infty$ as $w$ tends to any point of $\Gamma$. Then the action of the boundary loop of $u$ is at most the positive part of the $d\lambda_0$-area of $e$:
--   $$\int_0^1 \lambda_0\Big(u(e^{2\pi i t})\Big)\Big[\tfrac{d}{dt}\, u(e^{2\pi i t})\Big]\, dt \;\le\; \int_D \max\big(\omega_0(\partial_s e, \partial_t e), 0\big)\, ds\, dt .$$
--
--   Role: the area part of the energy estimate $E \le \mathrm{area}(e)$ for disks with boundary on a special spanning disk (Hryniewicz 2014, Section 3.2), used for the compactness of the Bishop family.
--
--   Formalization Note: the left-hand side is `ENNReal.ofReal (loopAction H u (ccwLoop 1))`, the right-hand side `diskArea e`; the hypotheses are exactly those of `energy_le_diskArea`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), Section 3.2; H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), (26)-(27)

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), § 3.2; Hofer–Wysocki–Zehnder (1995), (26)–(27). Let `e` be a special spanning disk.
For a punctured `J̃`-holomorphic disk `u` with boundary on `e`, winding once around `e z₀`, with `a → -∞`
at every puncture, the action `∫ u*λ` of the boundary loop `t ↦ u(e^{2πit})` is at most the positive
part of the `dλ₀`-area of `e`. -/
theorem ofReal_loopAction_le_diskArea (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    ENNReal.ofReal (loopAction H u (ccwLoop 1)) ≤ diskArea e := by
  sorry

end FiniteEnergyPlane
