-- Prove2me | Theorems.Thm_EinsteinFieldEquations_schwarzschild_christoffel
-- name    : EinsteinFieldEquations.schwarzschild_christoffel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:45:19.911357+00:00
-- url     : https://prove2.me/theorems/5ff5d484-970f-4c3a-a9d5-23daad3a1ed5
-- title:
--   Christoffel symbols of the Schwarzschild metric
-- statement:
--   **Christoffel symbols of the Schwarzschild metric.** For $M > 0$ and a point of the exterior region ($r > 2M$, $0 < \theta < \pi$), with coordinates ordered $(t, r, \theta, \varphi)$, the Christoffel symbols of the second kind of the Schwarzschild metric take the classical values
--
--   $$\Gamma^{t}{}_{tr} = \Gamma^{t}{}_{rt} = \frac{M}{r(r-2M)}, \qquad \Gamma^{r}{}_{tt} = \frac{M(r-2M)}{r^{3}}, \qquad \Gamma^{r}{}_{rr} = -\frac{M}{r(r-2M)},$$
--
--   $$\Gamma^{r}{}_{\theta\theta} = -(r-2M), \qquad \Gamma^{r}{}_{\varphi\varphi} = -(r-2M)\sin^{2}\theta,$$
--
--   $$\Gamma^{\theta}{}_{r\theta} = \Gamma^{\varphi}{}_{r\varphi} = \frac{1}{r}, \qquad \Gamma^{\theta}{}_{\varphi\varphi} = -\sin\theta\cos\theta, \qquad \Gamma^{\varphi}{}_{\theta\varphi} = \frac{\cos\theta}{\sin\theta}.$$
--
--   These are the connection coefficients from which the Ricci tensor of the Schwarzschild metric is assembled.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations" (Schwarzschild solution); standard computation, e.g. S. Carroll, Spacetime and Geometry, ch. 5

import Definitions.Def_efe_metrics

namespace EinsteinFieldEquations

theorem schwarzschild_christoffel (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    christoffel (schwarzschild M) 0 0 1 x = M / (x 1 * (x 1 - 2 * M)) ∧
    christoffel (schwarzschild M) 0 1 0 x = M / (x 1 * (x 1 - 2 * M)) ∧
    christoffel (schwarzschild M) 1 0 0 x = M * (x 1 - 2 * M) / (x 1) ^ 3 ∧
    christoffel (schwarzschild M) 1 1 1 x = -(M / (x 1 * (x 1 - 2 * M))) ∧
    christoffel (schwarzschild M) 1 2 2 x = -(x 1 - 2 * M) ∧
    christoffel (schwarzschild M) 1 3 3 x = -(x 1 - 2 * M) * Real.sin (x 2) ^ 2 ∧
    christoffel (schwarzschild M) 2 1 2 x = 1 / x 1 ∧
    christoffel (schwarzschild M) 2 3 3 x = -(Real.sin (x 2) * Real.cos (x 2)) ∧
    christoffel (schwarzschild M) 3 1 3 x = 1 / x 1 ∧
    christoffel (schwarzschild M) 3 2 3 x = Real.cos (x 2) / Real.sin (x 2) := by sorry

end EinsteinFieldEquations
