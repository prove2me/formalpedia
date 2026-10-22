-- Prove2me | Theorems.Thm_FiniteEnergyPlane_omega0_tames_jtilde
-- name    : FiniteEnergyPlane.omega0_tames_jtilde
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:22:50.382872+00:00
-- url     : https://prove2.me/theorems/dfc120e7-badd-462c-a2ba-a4daf141f3b5
-- title:
--   The standard symplectic form is compatible with $\tilde J$
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. For every $y\neq0$: $\omega_0(v,\tilde J(y)v)>0$ for all $v\neq0$, and $\omega_0(\tilde J(y)v,\tilde J(y)w)=\omega_0(v,w)$ for all $v,w$.
--
--   **Formalization Note** $\omega_0$ is the constant form `omega0` on $V$ (not a form on $\mathbb{R}\times S$).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The standard symplectic form and the symplectization structure. At every `y ≠ 0`, `ω₀` is
compatible with `J̃(y)`: `ω₀(v, J̃ v) > 0` for `v ≠ 0`, and `ω₀(J̃ v, J̃ w) = ω₀(v, w)`. -/
theorem omega0_tames_jtilde {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y : V n) (hy : y ≠ 0) :
    (∀ v : V n, v ≠ 0 → 0 < omega0 v (Jtilde H J y v)) ∧
      ∀ v w : V n, omega0 (Jtilde H J y v) (Jtilde H J y w) = omega0 v w := by
  sorry

end FiniteEnergyPlane
