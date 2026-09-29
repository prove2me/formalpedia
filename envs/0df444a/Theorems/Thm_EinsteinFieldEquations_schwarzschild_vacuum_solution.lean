-- Prove2me | Theorems.Thm_EinsteinFieldEquations_schwarzschild_vacuum_solution
-- name    : EinsteinFieldEquations.schwarzschild_vacuum_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:51:10.692164+00:00
-- url     : https://prove2.me/theorems/3af31561-8c25-4a27-9dba-0aa5cf4a0917
-- title:
--   The Schwarzschild metric solves the vacuum Einstein field equations
-- statement:
--   **Goal theorem.** For $M > 0$, at every point of the exterior region ($r > 2M$, $0 < \theta < \pi$), the Schwarzschild metric
--
--   $$g \;=\; \operatorname{diag}\!\left(-\left(1-\frac{2M}{r}\right),\ \left(1-\frac{2M}{r}\right)^{-1},\ r^{2},\ r^{2}\sin^{2}\theta\right)$$
--
--   satisfies the Einstein field equations with vanishing cosmological constant and vanishing stress–energy tensor:
--
--   $$G_{ab} + 0 \cdot g_{ab} \;=\; \kappa \cdot 0 \qquad \text{for all } a,b \in \{0,1,2,3\},$$
--
--   for every value of the Einstein gravitational constant $\kappa$. In words: the Schwarzschild metric is an exact vacuum solution of the Einstein field equations on its exterior region — the first non-trivial exact solution of the equations, found by Schwarzschild in 1916.
-- source:
--   Wikipedia, "General relativity", https://en.wikipedia.org/wiki/General_relativity, section "History" and "Solutions" ("Karl Schwarzschild found the first non-trivial exact solution to the Einstein field equations, the Schwarzschild metric"); Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations"

import Definitions.Def_efe_metrics

namespace EinsteinFieldEquations

theorem schwarzschild_vacuum_solution (M : ℝ) (kappa : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    SatisfiesEFE (schwarzschild M) 0 kappa (fun _ => 0) x := by sorry

end EinsteinFieldEquations
