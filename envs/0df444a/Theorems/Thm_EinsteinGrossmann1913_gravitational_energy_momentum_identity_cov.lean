-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_gravitational_energy_momentum_identity_cov
-- name    : EinsteinGrossmann1913.gravitational_energy_momentum_identity_cov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:27.582978+00:00
-- url     : https://prove2.me/theorems/dc1fea86-713b-463e-bb28-714a138c7ef4
-- title:
--   Identity (12b): covariant form of the gravitational energy-momentum identity
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, $g<0$), $\gamma_{\mu\nu}$ its reciprocal, and $\kappa\neq0$. With $t_{\mu\nu}$ the covariant stress-energy tensor of the gravitational field (eq. (14)) and $D_{\mu\nu}(g)$ the operator of eq. (16), for every $\sigma$ and every point,
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\Big\{\sqrt{-g}\,\gamma_{\mu\nu}\,\kappa t_{\mu\sigma}\Big\}=\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial\gamma_{\mu\nu}}{\partial x_\sigma}\Big\{-D_{\mu\nu}(g)-\kappa t_{\mu\nu}\Big\}.$$
--
--   This is the covariant counterpart of (12a); it underlies the covariant field equations (21) and the conservation law (22).
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, p. 16, eqs. (14), (16) and (12b).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem gravitational_energy_momentum_identity_cov (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
        pd ν (fun y => sqrtNegDet g y * gamma g y μ ν * (κ * gravStressEnergyCov κ g y μ σ)) x
      = (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
          sqrtNegDet g x * pd σ (fun y => gamma g y μ ν) x
            * (-entwurfD g x μ ν - κ * gravStressEnergyCov κ g x μ ν) := by sorry

end EinsteinGrossmann1913
