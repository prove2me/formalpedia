-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_total_conservation
-- name    : EinsteinGrossmann1913.total_conservation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:02:38.766392+00:00
-- url     : https://prove2.me/theorems/2c3e45c3-2973-4d85-ab22-db52f991f54f
-- title:
--   Eq. (19): matter and gravitational field together satisfy the conservation laws
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, $g=\det(g_{\mu\nu})<0$), let $\kappa\neq0$, and let $\Theta_{\mu\nu}$ be a continuously differentiable contravariant stress-energy tensor of a material process such that
--
--   1. the energy-momentum law of matter (10) holds:
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\big(\sqrt{-g}\,g_{\sigma\mu}\Theta_{\mu\nu}\big)-\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial g_{\mu\nu}}{\partial x_\sigma}\Theta_{\mu\nu}=0;$$
--   2. the Entwurf gravitational field equations (18) hold: $\Delta_{\mu\nu}(\gamma)=\kappa(\Theta_{\mu\nu}+\vartheta_{\mu\nu})$, with $\vartheta_{\mu\nu}$ the stress-energy tensor of the gravitational field, eq. (13), and $\Delta_{\mu\nu}$ the operator of eq. (15).
--
--   Then for every $\sigma=1,2,3,4$ and every point
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\Big\{\sqrt{-g}\,g_{\sigma\mu}\,(\Theta_{\mu\nu}+\vartheta_{\mu\nu})\Big\}=0.$$
--
--   In the words of the source: “Hieraus ersieht man, daß für Materie und Gravitationsfeld zusammen die Erhaltungssätze gelten.” The gravitational stress-energy $\vartheta_{\mu\nu}$ enters the field equations in the same way as $\Theta_{\mu\nu}$, and the total energy-momentum of matter and field is conserved.
--
--   **Formalization Note** Everything is stated in one global chart on $\mathbb R^4$; $\Theta$ is assumed $C^1$ so that the derivatives in (10) and in the conclusion are genuine derivatives.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, p. 17, eq. (19), derived from eqs. (10), (12a) and (18).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem total_conservation (κ : ℝ) (hκ : κ ≠ 0) (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ μ ν : Fin 4, ContDiff ℝ 1 (fun x => Θ x μ ν))
    (h10 : MatterConservation g Θ) (h18 : EntwurfFieldEquations κ g Θ)
    (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
      pd ν (fun y => sqrtNegDet g y * g y σ μ
        * (Θ y μ ν + gravStressEnergy κ g y μ ν)) x = 0 := by sorry

end EinsteinGrossmann1913
