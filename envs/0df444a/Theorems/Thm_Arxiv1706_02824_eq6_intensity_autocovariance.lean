-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq6_intensity_autocovariance
-- name    : Arxiv1706_02824.eq6_intensity_autocovariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:48:45.620291+00:00
-- url     : https://prove2.me/theorems/e8357c73-d6b1-4efa-a41f-132afe54bebb
-- title:
--   Eq. (6): intensity autocovariance of finite exposures of polychromatic light
-- statement:
--   Let $U(x,t)$ be a field whose complex amplitudes have circular Gaussian statistics, measurable jointly in time and in the sample. Suppose it has a cross-spectral density $W(x_1,x_2,\nu)$, integrable in $\nu$, with
--   $$\langle U(x_1,t_1)U^*(x_2,t_2)\rangle=\int W(x_1,x_2,\nu)\,e^{i2\pi\nu(t_1-t_2)}\,d\nu .$$
--   Let $T>0$ and $I_T(x)=T^{-1}\int_{-T/2}^{T/2}|U(x,t)|^2\,dt$. Then $\langle I_T(x)\rangle=\int S(x,\nu)\,d\nu$ with $S(x,\nu)=W(x,x,\nu)$ for every $x$. Moreover (eq. A8)
--   $$\langle I_T(x_1)I_T(x_2)\rangle=\int S(x_1,\nu_1)\,d\nu_1\int S(x_2,\nu_2)\,d\nu_2+\iint W(x_1,x_2,\nu_1)W^*(x_1,x_2,\nu_2)\,\mathrm{sinc}^2[\pi(\nu_1-\nu_2)T]\,d\nu_1d\nu_2,$$
--   and therefore (eq. 6)
--   $$C_T(x_1,x_2)=\iint W(x_1,x_2,\nu_1)W^*(x_1,x_2,\nu_2)\,\mathrm{sinc}^2[\pi(\nu_1-\nu_2)T]\,d\nu_1d\nu_2 .$$
--
--   This extends eq. (5), $C=|J|^2$, to finite exposures of polychromatic light.
--
--   **Formalization Note** The field is taken directly in the plane where the intensity is measured, so the plane $z=R$ is not a separate parameter. The paper assumes circular Gaussian statistics in the source plane and propagates linearly; a linear image of a circular Gaussian field is again circular Gaussian. The spectral representation encodes wide-sense stationarity. Ergodicity is not a separate hypothesis: a stationary Gaussian process with an absolutely continuous spectrum is mixing.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c001; Section 2, eq. (6), derived in the Appendix as eqs. (A1)-(A9), PDF pp. 2 and 7-8

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq6_intensity_autocovariance {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (U : ℝ × ℝ → Omega → ℂ) (hU : IsCircularGaussian P U)
    (hmeas : ∀ x : ℝ, Measurable (fun p : ℝ × Omega => U (x, p.1) p.2))
    (W : ℝ → ℝ → ℝ → ℂ) (hW : IsCrossSpectralDensity P U W)
    (T : ℝ) (hT : 0 < T) (x1 x2 : ℝ) :
    (∀ x : ℝ, ((∫ w, timeAvgIntensity U T x w ∂P : ℝ) : ℂ) = ∫ ν : ℝ, W x x ν) ∧
    ((∫ w, timeAvgIntensity U T x1 w * timeAvgIntensity U T x2 w ∂P : ℝ) : ℂ) =
      (∫ ν : ℝ, W x1 x1 ν) * (∫ ν : ℝ, W x2 x2 ν) + sincSqIntegral (W x1 x2) T ∧
    ((intensityAutocov P U T x1 x2 : ℝ) : ℂ) = sincSqIntegral (W x1 x2) T := by sorry

end Arxiv1706_02824
