-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_matterConservation_iff_cov
-- name    : EinsteinGrossmann1913.matterConservation_iff_cov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:00:18.158021+00:00
-- url     : https://prove2.me/theorems/842ceaed-0cc7-4209-9df7-5b29d9695d27
-- title:
--   Eq. (10) ⇔ eq. (20): covariant form of the energy-momentum law of matter
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, $g<0$), and let $\Theta_{\mu\nu}$ be a symmetric, continuously differentiable contravariant stress-energy tensor of a material process. Put $T_{\mu\nu}=\sum_{\alpha\beta}g_{\mu\alpha}g_{\nu\beta}\Theta_{\alpha\beta}$. Then the energy-momentum law (10),
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\big(\sqrt{-g}\,g_{\sigma\mu}\Theta_{\mu\nu}\big)-\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial g_{\mu\nu}}{\partial x_\sigma}\Theta_{\mu\nu}=0\qquad(\sigma=1,\dots,4),$$
--
--   holds everywhere if and only if its covariant form (20),
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\big(\sqrt{-g}\,\gamma_{\mu\nu}T_{\mu\sigma}\big)+\tfrac12\sum_{\mu\nu}\sqrt{-g}\,\frac{\partial\gamma_{\mu\nu}}{\partial x_\sigma}T_{\mu\nu}=0\qquad(\sigma=1,\dots,4),$$
--
--   holds everywhere.
--
--   **Formalization Note** The source obtains (20) from (10) “durch gliedweise Umformung”; the symmetry of $\Theta_{\mu\nu}$ (true for the source's stress-energy tensors, e.g. $\Theta_{\mu\nu}=\varrho_0\frac{dx_\mu}{ds}\frac{dx_\nu}{ds}$) is stated explicitly, as is the differentiability of $\Theta$.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §4, p. 10, eq. (10), and §5, p. 17, definition of T_{μν} and eq. (20).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem matterConservation_iff_cov (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ μ ν : Fin 4, ContDiff ℝ 1 (fun x => Θ x μ ν))
    (hΘsymm : ∀ (x : Coord) (μ ν : Fin 4), Θ x μ ν = Θ x ν μ) :
    MatterConservation g Θ ↔ MatterConservationCov g (lowerIndices g Θ) := by sorry

end EinsteinGrossmann1913
