-- Prove2me | Theorems.Thm_EinsteinGrossmann1913_total_conservation_cov
-- name    : EinsteinGrossmann1913.total_conservation_cov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:01:30.740416+00:00
-- url     : https://prove2.me/theorems/95a0e7da-fe18-4b68-8cf4-ea2395fc978d
-- title:
--   Eq. (22): conservation for matter and gravitational field, covariant form
-- statement:
--   Let $g_{\mu\nu}$ be a fundamental tensor on $\mathbb R^4$ (twice continuously differentiable, symmetric, $g<0$), $\kappa\neq0$, and $T_{\mu\nu}$ a continuously differentiable covariant stress-energy tensor of matter satisfying the covariant energy-momentum law (20) and the covariant field equations (21). Then for every $\sigma$ and every point
--
--   $$\sum_{\mu\nu}\frac{\partial}{\partial x_\nu}\Big\{\sqrt{-g}\,\gamma_{\mu\nu}\,(T_{\mu\sigma}+t_{\mu\sigma})\Big\}=0.$$
--
--   This is the covariant analogue of (19): matter and gravitational field together satisfy conservation laws.
--
--   **Formalization Note** The source prints (22) as $\sum_\nu\frac{\partial}{\partial x_\nu}\{\sqrt{-g}\cdot\gamma_{\sigma\mu}(T_{\mu\nu}+t_{\mu\nu})\}=0$, in which the index $\mu$ occurs twice but is not listed under the summation sign and the free index $\sigma$ sits on $\gamma$. The statement here uses the index placement of (20) and (12b), from which the source says (22) follows “analog (19)”; reviewers should check this reading.
-- source:
--   A. Einstein and M. Grossmann, "Entwurf einer verallgemeinerten Relativitätstheorie und einer Theorie der Gravitation", B. G. Teubner, Leipzig und Berlin 1913 (Separatabdruck aus Zeitschrift für Mathematik und Physik 62), Part I (Physikalischer Teil, A. Einstein), §5, p. 17, eq. (22) (index placement corrected, see Formalization Note).

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs

namespace EinsteinGrossmann1913

theorem total_conservation_cov (κ : ℝ) (hκ : κ ≠ 0) (g T : Field2) (hg : IsMetricField g)
    (hT : ∀ μ ν : Fin 4, ContDiff ℝ 1 (fun x => T x μ ν))
    (h20 : MatterConservationCov g T) (h21 : EntwurfFieldEquationsCov κ g T)
    (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
      pd ν (fun y => sqrtNegDet g y * gamma g y μ ν
        * (T y μ σ + gravStressEnergyCov κ g y μ σ)) x = 0 := by sorry

end EinsteinGrossmann1913
