-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_lt_infDist_proj_le_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_lt_infDist_proj_le_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:13:14.29521+00:00
-- url     : https://prove2.me/theorems/abaa9ed8-7dff-4214-967a-add34f5d6e8d
-- title:
--   A fast plane approaches its orbit faster than the window rate
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $\tilde J$ the induced almost complex structure on $\mathbb{R}^4 \setminus \{0\}$, and $P = (x, T)$ a periodic Reeb orbit (not assumed nondegenerate). Let $\delta \in \mathbb{R}$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$, in the global frame of $\xi$.
--
--   Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be a fast finite-energy plane whose puncture $\infty$ is nondegenerate with asymptotic limit $P$, and let $\pi$ denote the radial projection to $S$. Then there are $\mu < \delta$ and $C$ such that
--   $$\operatorname{dist}\big(\pi(u(z)), x(\mathbb{R})\big) \le C\,(1 + |z|)^{\mu/2\pi} \quad \text{for all } z \in \mathbb{C}.$$
--
--   Role: a decay rate strictly faster than the window rate $(1+|z|)^{\delta/2\pi}$, needed where a rate exactly at the window must be reached after a small loss.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ is `proj H`, the distance is `infDist`; the window hypothesis is stated with `HasEigenWind J P μ k`; "fast" is `IsFastPlane H J u` and the end is `IsNondegenerateEnd H u cylInf P 1`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Theorem 2.11 and Section 2

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A fast plane approaches its orbit faster than the window rate. Let `u` be a fast
finite-energy plane with a nondegenerate end at `P`, and let `δ` be such that every eigenvalue of
`A_P` below `δ` has winding at most `1` and every eigenvalue above `δ` has winding at least `2`.
Then for some `μ < δ` and `C` the distance from `proj (u z)` to the image of `P` is at most
`C (1 + ‖z‖)^{μ/2π}` for all `z`. -/
theorem exists_lt_infDist_proj_le_of_isFastPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)) := by
  sorry

end FiniteEnergyPlane
