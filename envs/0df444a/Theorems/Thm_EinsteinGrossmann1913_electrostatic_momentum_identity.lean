-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_electrostatic_momentum_identity
-- name    : EinsteinGrossmann1913.electrostatic_momentum_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:22.678853+00:00
-- url     : https://prove2.me/theorems/e3153444-9b85-4e44-a400-a61e1b59d5ec
-- title:
--   Electrostatic model identity for the momentum law (p. 14)
-- statement:
--   Let $\varphi:\mathbb R^3\to\mathbb R$ be a twice continuously differentiable function (the electrostatic potential). Then for every $\nu\in\{1,2,3\}$ and every point $x$,
--
--   $$\sum_{\mu}\frac{\partial}{\partial x_\mu}\Big(\frac{\partial\varphi}{\partial x_\nu}\frac{\partial\varphi}{\partial x_\mu}\Big)-\frac{\partial}{\partial x_\nu}\Big(\tfrac12\sum_\mu\Big(\frac{\partial\varphi}{\partial x_\mu}\Big)^2\Big)=\frac{\partial\varphi}{\partial x_\nu}\sum_\mu\frac{\partial^2\varphi}{\partial x_\mu^2}.$$
--
--   In the source this identity is the model for the method by which the gravitational field equations are found: if $\varphi$ satisfies $\sum_\mu\partial^2\varphi/\partial x_\mu^2=\varrho$, the right-hand side equals $\frac{\partial\varphi}{\partial x_\nu}\varrho$, the negative of the momentum $-\frac{\partial\varphi}{\partial x_\nu}\varrho$ transferred to the charges, so the momentum law takes the form of a sum of derivatives.
--
--   **Formalization Note** Only the identity itself is stated; the Poisson equation is not assumed.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, p. 14 (electrostatic example illustrating the method).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem electrostatic_momentum_identity (φ : (Fin 3 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (ν : Fin 3) (x : Fin 3 → ℝ) :
    (∑ μ : Fin 3, pd μ (fun y => pd ν φ y * pd μ φ y) x)
      - pd ν (fun y => (1 / 2) * ∑ μ : Fin 3, (pd μ φ y) ^ 2) x
      = pd ν φ x * ∑ μ : Fin 3, pd μ (pd μ φ) x := by sorry

end EinsteinGrossmann1913
