-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_sub
-- name    : FiniteEnergyPlane.exists_equiv_hasStrictFDerivAt_exp_smul_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:04:39.845362+00:00
-- url     : https://prove2.me/theorems/2754f6d7-4030-438d-9c1c-d8fdf659f972
-- title:
--   Nondegeneracy of the intersection equation of a plane through a Reeb trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$, $y$ a Reeb trajectory, $t_0\in\mathbb{R}$, and $u_0:\mathbb{C}\to\mathbb{R}^4$ a $C^1$ map with $u_0(0)=y(t_0)$ such that $D(\mathrm{pr}_S\circ u_0)(0)\,v$ is not a real multiple of $R(\mathrm{pr}_S u_0(0))$ for any $v\ne0$. Then the map $F(s,z,t)=e^{2s}u_0(z)-y(t)$ on $\mathbb{R}\times\mathbb{C}\times\mathbb{R}$ is strictly differentiable at $(0,0,t_0)$, and its derivative there,
--   $$(\delta s,\delta z,\delta t)\mapsto 2\,\delta s\,u_0(0)+Du_0(0)\,\delta z-\delta t\,R(u_0(0)),$$
--   is a linear isomorphism $\mathbb{R}\times\mathbb{C}\times\mathbb{R}\to\mathbb{R}^4$.
--
--   In words: the radial direction, the tangent plane of $u_0$ at $0$ and the Reeb direction span $\mathbb{R}^4$ at $y(t_0)$, so the equation $e^{2s}u_0(z)=y(t)$ is nondegenerate at $(0,0,t_0)$. It is used to locate the intersections of Reeb trajectories with nearby fast planes (Hryniewicz 2012, Lemmas 7.2 and 7.3).
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, $\mathrm{pr}_S$ is `proj H`, $R$ is `reeb H`, and the trajectory hypothesis is `IsReebTrajectory H y`. The isomorphism is a `ContinuousLinearEquiv` whose values are given by the displayed formula, and strict differentiability is `HasStrictFDerivAt`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemmas 7.2 and 7.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `S = H⁻¹(1)` be strictly star-shaped, `y` a Reeb trajectory and `u₀ : ℂ → V 1` a `C¹` map with
`u₀ 0 = y t₀`, such that `D(proj ∘ u₀)(0) v` is never a multiple of the Reeb vector at `proj (u₀ 0)`
for `v ≠ 0`. Then `(s, z, t) ↦ e^{2s} u₀(z) - y(t)` has, at `(0, 0, t₀)`, a strict derivative that is a
linear isomorphism `ℝ × ℂ × ℝ ≃ V 1`, namely `(δs, δz, δt) ↦ 2δs u₀(0) + Du₀(0) δz - δt R(u₀(0))`. -/
theorem exists_equiv_hasStrictFDerivAt_exp_smul_sub (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀) (y : ℝ → V 1)
    (hy : IsReebTrajectory H y) (t₀ : ℝ) (h0 : u₀ 0 = y t₀)
    (htr : ∀ v : ℂ, v ≠ 0 → ∀ c : ℝ,
      fderiv ℝ (fun z => proj H (u₀ z)) 0 v ≠ c • reeb H (proj H (u₀ 0))) :
    ∃ L : (ℝ × ℂ × ℝ) ≃L[ℝ] V 1,
      (∀ q : ℝ × ℂ × ℝ, L q = (2 * q.1) • u₀ 0 + fderiv ℝ u₀ 0 q.2.1 - q.2.2 • reeb H (u₀ 0)) ∧
      HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • u₀ q.2.1 - y q.2.2)
        (L : ℝ × ℂ × ℝ →L[ℝ] V 1) ((0 : ℝ), (0 : ℂ), t₀) := by
  sorry

end FiniteEnergyPlane
