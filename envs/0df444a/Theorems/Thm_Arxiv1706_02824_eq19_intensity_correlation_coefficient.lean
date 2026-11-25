-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq19_intensity_correlation_coefficient
-- name    : Arxiv1706_02824.eq19_intensity_correlation_coefficient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:15:26.352479+00:00
-- url     : https://prove2.me/theorems/8c874e9c-21f2-4c37-86f8-4fc4fc9c456a
-- title:
--   Eqs. (19)-(20): far-field correlation coefficient of intensities
-- statement:
--   Let the quasi-monochromatic detector-plane amplitudes $V(x)$ have circular Gaussian statistics. Let their mutual intensity have the far-field form, for all $y_1,y_2$,
--   $$J_R(y_1,y_2)=\langle V^*(y_1)V(y_2)\rangle=\frac{e^{i\pi(y_1^2-y_2^2)/(\lambda R)}}{\lambda R}\,\hat S_0\Big(\frac{y_1-y_2}{\lambda R}\Big)\hat g_0\Big(\frac{y_1+y_2}{2\lambda R}\Big),$$
--   with $\lambda,R>0$, $S_0\ge0$ and $g_0(0)=1$. If $\langle I_R(x_1)\rangle>0$ and $\langle I_R(x_2)\rangle>0$, then
--   $$c^{(2,2)}(x_1,x_2)=\frac{C_R(x_1,x_2)}{[C_R(x_1,x_1)C_R(x_2,x_2)]^{1/2}}=\frac{\big|\hat S_0\big(\frac{x_1-x_2}{\lambda R}\big)\big|^2\big|\hat g_0\big(\frac{x_1+x_2}{2\lambda R}\big)\big|^2}{|\hat S_0(0)|^2\,\big|\hat g_0\big(\frac{x_1}{\lambda R}\big)\hat g_0\big(\frac{x_2}{\lambda R}\big)\big|}=|\gamma^{(1,1)}(x_1,x_2)|^2 .$$
--   Here $\gamma^{(1,1)}=J_R/(\langle I_R(x_1)\rangle^{1/2}\langle I_R(x_2)\rangle^{1/2})$ equals the correlation coefficient $c^{(1,1)}$ of the complex amplitudes (eq. 20).
--
--   **Formalization Note** "Quasi-monochromatic" means a single frequency, so $\lambda$ is a fixed positive number. The far-field form of $J_R$ is the frequency-free version of eq. (10). Positivity of the mean intensities, implicit in the paper's divisions, is a hypothesis.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c014; Section 5, eqs. (19)-(20), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq19_intensity_correlation_coefficient {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (V : ℝ → Omega → ℂ) (hV : IsCircularGaussian P V)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (S0 : ℝ → ℝ) (g0 : ℝ → ℂ) (hS0 : ∀ y, 0 ≤ S0 y) (hg0 : g0 0 = 1)
    (hJ : ∀ y1 y2 : ℝ, mutualIntensity P V y1 y2 =
      Complex.exp (Complex.I * ((π * (y1 ^ 2 - y2 ^ 2) / (lam * R) : ℝ) : ℂ)) /
          ((lam * R : ℝ) : ℂ) *
        ft (fun y => (S0 y : ℂ)) ((y1 - y2) / (lam * R)) * ft g0 ((y1 + y2) / (2 * lam * R)))
    (x1 x2 : ℝ) (h1 : 0 < meanIntensity P V x1) (h2 : 0 < meanIntensity P V x2) :
    intensityCorrCoeff P V x1 x2 =
      ‖ft (fun y => (S0 y : ℂ)) ((x1 - x2) / (lam * R))‖ ^ 2 *
          ‖ft g0 ((x1 + x2) / (2 * lam * R))‖ ^ 2 /
        (‖ft (fun y => (S0 y : ℂ)) 0‖ ^ 2 *
          ‖ft g0 (x1 / (lam * R)) * ft g0 (x2 / (lam * R))‖) ∧
    intensityCorrCoeff P V x1 x2 = ‖coherenceFactor11 P V x1 x2‖ ^ 2 ∧
    coherenceFactor11 P V x1 x2 = ampCorrCoeff P V x1 x2 := by sorry

end Arxiv1706_02824
