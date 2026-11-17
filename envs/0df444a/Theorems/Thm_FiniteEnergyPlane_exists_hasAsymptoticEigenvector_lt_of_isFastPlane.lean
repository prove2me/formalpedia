-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_lt_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_hasAsymptoticEigenvector_lt_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:10:34.388312+00:00
-- url     : https://prove2.me/theorems/95bf8e08-5f3d-41e8-87d8-4dff47e7d2c0
-- title:
--   The asymptotic eigenvalue of a fast plane lies below a spectral window
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $\tilde J$ the induced almost complex structure on $\mathbb{R}^4 \setminus \{0\}$, and $P = (x, T)$ a periodic Reeb orbit (not assumed nondegenerate). Let $\delta \in \mathbb{R}$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$, in the global frame of $\xi$.
--
--   Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be a fast finite-energy plane whose puncture $\infty$ is nondegenerate with asymptotic limit $P$. Then $u$ has an asymptotic eigenvalue $\mu < \delta$ with an asymptotic eigenvector of $A_P$ at $\infty$, in the cylindrical coordinates $z = e^{2\pi(s+it)}$.
--
--   Role: places the asymptotic eigenvalue of a fast plane strictly below a spectral window; used for decay rates of fast planes and of graphs over them in a tube.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`; the window hypothesis is stated with `HasEigenWind J P μ k`; "fast" is `IsFastPlane H J u`, the nondegenerate end is `IsNondegenerateEnd H u cylInf P 1`, and the conclusion is `HasAsymptoticEigenvector H J u cylInf P 1 μ v` (Hryniewicz, Theorem 2.11, along `cylInf`).
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Theorem 2.11 and Section 2

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The asymptotic eigenvalue of a fast plane lies below the window. Let `u` be a fast
finite-energy plane with a nondegenerate end at `P`, and let `δ` be such that every eigenvalue of
`A_P` below `δ` has winding at most `1` and every eigenvalue above `δ` has winding at least `2`.
Then `u` has an asymptotic eigenvalue `μ < δ` with an asymptotic eigenvector at `∞`, in the
cylindrical coordinates `cylInf`. -/
theorem exists_hasAsymptoticEigenvector_lt_of_isFastPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ μ < δ, ∃ v : ℝ → V 1, HasAsymptoticEigenvector H J u cylInf P 1 μ v := by
  sorry

end FiniteEnergyPlane
