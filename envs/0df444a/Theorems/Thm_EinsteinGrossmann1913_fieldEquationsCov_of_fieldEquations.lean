-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_fieldEquationsCov_of_fieldEquations
-- name    : EinsteinGrossmann1913.fieldEquationsCov_of_fieldEquations
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:00:47.961154+00:00
-- url     : https://prove2.me/theorems/ffcc7ea7-a7cd-4bd7-94a0-ce21f12de704
-- title:
--   Eq. (18) ⇒ eq. (21): covariant form of the Entwurf field equations
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, $g<0$), $\kappa\neq0$, and $\Theta_{\mu\nu}$ any contravariant tensor field such that the Entwurf field equations (18)
--
--   $$\Delta_{\mu\nu}(\gamma)=\kappa\,(\Theta_{\mu\nu}+\vartheta_{\mu\nu})$$
--
--   hold everywhere. Then, with $T_{\mu\nu}=\sum_{\alpha\beta}g_{\mu\alpha}g_{\nu\beta}\Theta_{\alpha\beta}$, the covariant field equations (21)
--
--   $$-D_{\mu\nu}(g)=\kappa\,(t_{\mu\nu}+T_{\mu\nu})$$
--
--   hold everywhere.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, p. 17, eqs. (18) and (21) ("welche Gleichungen auch direkt aus (18) abgeleitet werden können").

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem fieldEquationsCov_of_fieldEquations (κ : ℝ) (hκ : κ ≠ 0) (g Θ : Field2)
    (hg : IsMetricField g) (h18 : EntwurfFieldEquations κ g Θ) :
    EntwurfFieldEquationsCov κ g (lowerIndices g Θ) := by sorry

end EinsteinGrossmann1913
