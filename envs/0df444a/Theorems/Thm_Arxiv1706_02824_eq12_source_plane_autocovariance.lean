-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq12_source_plane_autocovariance
-- name    : Arxiv1706_02824.eq12_source_plane_autocovariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:01:31.174691+00:00
-- url     : https://prove2.me/theorems/1618ac75-bb30-40b3-b151-198f4d274a00
-- title:
--   Eq. (12): intensity autocovariance in the source plane
-- statement:
--   Let the source-plane field satisfy the hypotheses of eq. (6) with cross-spectral density $W_0$, and let $W_0$ follow the quasi-homogeneous model (9),
--   $$W_0(x_1',x_2',\nu)=S_0\Big(\frac{x_1'+x_2'}2,\nu\Big)g_0(x_1'-x_2',\nu),\qquad S_0\ge0,\ g_0(0,\nu)=1 .$$
--   If $W_0(x_1',x_2',\cdot)$ is square-integrable, then
--   $$T\,C_{T,0}(x_1',x_2')\ \longrightarrow\ \int S_0\Big(\frac{x_1'+x_2'}2,\nu\Big)^2\,\big|g_0(x_1'-x_2',\nu)\big|^2\,d\nu\qquad(T\to\infty).$$
--
--   In the source plane the mean coordinate enters through the spectral density and the difference coordinate through the degree of coherence, the reverse of eq. (11).
--
--   **Formalization Note** Eq. (12), $C_{T,0}\cong T^{-1}\int\cdots d\nu$, is stated as the limit of $T\,C_{T,0}$ for long exposures (eq. 8). The width conditions on $S_0$ and $g_0$ are needed only for eq. (10), so they are not hypotheses here.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c007; Section 3, eqs. (9) and (12), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq12_source_plane_autocovariance {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (U : ℝ × ℝ → Omega → ℂ) (hU : IsCircularGaussian P U)
    (hmeas : ∀ x : ℝ, Measurable (fun p : ℝ × Omega => U (x, p.1) p.2))
    (W0 : ℝ → ℝ → ℝ → ℂ) (hW : IsCrossSpectralDensity P U W0)
    (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (hqh : IsQuasiHomogeneous W0 S0 g0)
    (x1 x2 : ℝ) (hW2 : MemLp (W0 x1 x2) 2) :
    Tendsto (fun T : ℝ => T * intensityAutocov P U T x1 x2) atTop
      (𝓝 (∫ ν : ℝ, S0 ((x1 + x2) / 2) ν ^ 2 * ‖g0 (x1 - x2) ν‖ ^ 2)) := by sorry

end Arxiv1706_02824
