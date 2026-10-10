-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_gravitational_energy_momentum_identity
-- name    : EinsteinGrossmann1913.gravitational_energy_momentum_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:54.648502+00:00
-- url     : https://prove2.me/theorems/43a66d3a-0d78-4c23-a44f-620088c1848b
-- title:
--   Identity (12a): the gravitational energy-momentum identity
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, with $g=\det(g_{\mu\nu})<0$), let $\gamma_{\mu\nu}$ be its reciprocal, and let $\kappa\neq0$. With $\vartheta_{\mu\nu}$ the stress-energy tensor of the gravitational field (eq. (13)) and $\Delta_{\mu\nu}(\gamma)$ the operator of eq. (15), for every $\sigma=1,2,3,4$ and every point,
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\Big\{\sqrt{-g}\,g_{\sigma\mu}\,\kappa\vartheta_{\mu\nu}\Big\}=\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial g_{\mu\nu}}{\partial x_\sigma}\Big\{-\Delta_{\mu\nu}(\gamma)+\kappa\vartheta_{\mu\nu}\Big\}.$$
--
--   This is the identity (12) of the paper rewritten with the abbreviations (13) and (15). It is a pure differential identity in $g_{\mu\nu}$, valid for every metric field, and it is the step from which the field equations (18) and the conservation law (19) are read off.
--
--   **Formalization Note** $\kappa\vartheta_{\mu\nu}$ does not depend on $\kappa$; $\kappa\neq0$ is assumed because $\vartheta_{\mu\nu}$ is defined with the factor $1/(2\kappa)$.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, pp. 15–16, eqs. (12), (13), (15) and (12a).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem gravitational_energy_momentum_identity (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
        pd ν (fun y => sqrtNegDet g y * g y σ μ * (κ * gravStressEnergy κ g y μ ν)) x
      = (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
          sqrtNegDet g x * pd σ (fun y => g y μ ν) x
            * (-entwurfDelta g x μ ν + κ * gravStressEnergy κ g x μ ν) := by sorry

end EinsteinGrossmann1913
