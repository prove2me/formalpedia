-- Prove2me | Theorems.Thm_FiniteEnergyPlane_infDist_proj_le_of_isFastPlane
-- name    : FiniteEnergyPlane.infDist_proj_le_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T14:21:59.974417+00:00
-- url     : https://prove2.me/theorems/1c2ff730-60ed-410b-8eb2-9befc90dd493
-- title:
--   A fast plane approaches its asymptotic orbit at a spectral-gap rate
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, $P=(x,T)$ a periodic Reeb orbit, and let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be a fast finite-energy $\tilde J$-holomorphic plane (Hryniewicz, Definition 2.14) whose puncture $\infty$ is nondegenerate (Definition 2.9) with asymptotic limit $P$. Let $\delta<0$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue of $A_P$ above $\delta$ has winding number at least $2$. Then there is a constant $C$ such that
--   $$\operatorname{dist}\big(\mathrm{proj}(u(z)),\,x(\mathbb R)\big)\le C\,(1+|z|)^{\delta/2\pi}\qquad\text{for all } z\in\mathbb C.$$
--
--   The statement gives the rate at which a fast plane approaches the image of its asymptotic orbit, measured against a spectral gap $\delta$ of $A_P$. It is the upper-bound counterpart of the corresponding lower bound, and supplies the decay hypothesis on the base plane in the construction of families of fast planes (Hryniewicz, Trans. AMS 2012, Lemmas 6.10 and 6.20).
--
--   Formalization Note: `proj H` is the radial projection onto $S$; the distance is `Metric.infDist (proj H (u z)) (Set.range P.x)`. "Every eigenvalue below $\delta$ has winding at most 1 and every eigenvalue above $\delta$ has winding at least 2" is the hypothesis `∀ μ k, HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)`, where `HasEigenWind J P μ k` says that $\mu$ is an eigenvalue of $A_P$ all of whose eigenvectors have winding $k$ in the global frame of $\xi$.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6 (Lemmas 6.10, 6.20)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A fast plane approaches its asymptotic orbit at a window rate. Let `u` be a fast finite-energy
plane asymptotic to `P` at `∞`, and let `δ < 0` be such that every eigenvalue of `A_P` below `δ`
has winding number at most `1` and every eigenvalue above `δ` has winding number at least `2`.
Then for some `C` the distance from `proj (u z)` to the image of `P` is at most
`C (1 + ‖z‖)^{δ/2π}` for all `z`. -/
theorem infDist_proj_le_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  sorry

end FiniteEnergyPlane
