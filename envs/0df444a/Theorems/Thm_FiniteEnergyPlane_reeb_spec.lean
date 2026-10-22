-- Prove2me | Theorems.Thm_FiniteEnergyPlane_reeb_spec
-- name    : FiniteEnergyPlane.reeb_spec
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:22:33.678635+00:00
-- url     : https://prove2.me/theorems/b6b97b49-83c9-408a-9ca8-1cf494287d38
-- title:
--   The Reeb vector field of a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level and $x\in S$. Then $\lambda_0(x)X_H(x)>0$, and $R(x)=X_H(x)/\lambda_0(x)X_H(x)$ satisfies $\lambda_0(x)R(x)=1$, $dH(x)R(x)=0$, and $\omega_0(R(x),w)=0$ for every $w$ with $dH(x)w=0$.
--
--   **Formalization Note** $R$ is `reeb H x`; the tangent space $T_xS$ is $\ker dH(x)$, with `fderiv ℝ H x`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 1; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Reeb field of `λ₀|S` (Hofer 1993, § 1; Hryniewicz 2014, § 2.1). On a strictly
star-shaped level `S`, `λ₀(X_H) > 0`, and `R = X_H / λ₀(X_H)` is tangent to `S`, satisfies
`λ₀(R) = 1`, and `ω₀(R, w) = 0` for every `w ∈ T_x S`. -/
theorem reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  sorry

end FiniteEnergyPlane
