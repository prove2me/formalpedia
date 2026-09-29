-- Prove2me | Theorems.Thm_EinsteinFieldEquations_schwarzschild_inverse_metric
-- name    : EinsteinFieldEquations.schwarzschild_inverse_metric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:44:54.970185+00:00
-- url     : https://prove2.me/theorems/99b21de2-28db-4fae-bca4-c9cfb11f11e4
-- title:
--   Inverse of the Schwarzschild metric on the exterior
-- statement:
--   **Inverse Schwarzschild metric.** For $M > 0$ and a coordinate point in the exterior region ($r > 2M$, $0 < \theta < \pi$), the Schwarzschild metric matrix is invertible with inverse
--
--   $$g^{-1} \;=\; \operatorname{diag}\!\left(-\left(1-\frac{2M}{r}\right)^{-1},\; 1-\frac{2M}{r},\; \frac{1}{r^{2}},\; \frac{1}{r^{2}\sin^{2}\theta}\right).$$
--
--   This is the elementary but indispensable computation underlying every curvature quantity for the Schwarzschild metric, since Christoffel symbols and all traces are formed with the inverse metric.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations" (Schwarzschild solution); Wikipedia, "General relativity", https://en.wikipedia.org/wiki/General_relativity, section "Solutions"

import Definitions.Def_efe_metrics

namespace EinsteinFieldEquations

theorem schwarzschild_inverse_metric (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    (schwarzschild M x)⁻¹ = Matrix.diagonal ![-(1 - 2 * M / x 1)⁻¹, 1 - 2 * M / x 1,
      ((x 1) ^ 2)⁻¹, ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹] := by sorry

end EinsteinFieldEquations
