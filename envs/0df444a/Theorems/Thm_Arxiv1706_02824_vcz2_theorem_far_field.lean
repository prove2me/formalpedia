-- Prove2me | Theorems.Thm_Arxiv1706_02824_vcz2_theorem_far_field
-- name    : Arxiv1706_02824.vcz2_theorem_far_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:04:34.162011+00:00
-- url     : https://prove2.me/theorems/a8909861-ca15-4752-99eb-9b3f4760f9aa
-- title:
--   Eq. (11): van Cittert - Zernike theorem for intensity correlations (vCZ2 theorem)
-- statement:
--   **van Cittert - Zernike theorem for intensity correlations (vCZ2).** Let the detector-plane field $U_R(x,t)$ have circular Gaussian statistics and a cross-spectral density $W_R$, as in eq. (6). Let $S_0\ge0$ be the source spectral density and $g_0$ the spectral degree of coherence, $g_0(0,\nu)=1$. Let $c>0$, $R>0$ and $\lambda=c/\nu$. Suppose $W_R$ has the far-field form (10) at every frequency $\nu>0$,
--   $$W_R(x_1,x_2,\nu)=\frac{e^{i\psi}}{\lambda R}\,\hat S_0\Big(\frac{x_1-x_2}{\lambda R},\nu\Big)\,\hat g_0\Big(\frac{x_1+x_2}{2\lambda R},\nu\Big),\qquad \psi=\frac{\pi(x_1^2-x_2^2)}{\lambda R},$$
--   and vanishes for $\nu\le0$. If $W_R(x_1,x_2,\cdot)$ is square-integrable, then
--   $$T\,C_{T,R}(x_1,x_2)\ \longrightarrow\ \int_0^\infty\frac{1}{\lambda^2R^2}\Big|\hat S_0\Big(\frac{x_1-x_2}{\lambda R},\nu\Big)\Big|^2\Big|\hat g_0\Big(\frac{x_1+x_2}{2\lambda R},\nu\Big)\Big|^2d\nu\qquad(T\to\infty).$$
--
--   The far-field intensity autocovariance depends on the difference coordinate through the Fourier transform of the source spectral density, and on the mean coordinate through the Fourier transform of the degree of coherence. This is the reverse of eq. (12) in the source plane, and it is the basis of measuring source sizes by intensity interferometry.
--
--   **Formalization Note** Eq. (11), $C_{T,R}\cong T^{-1}\int\cdots d\nu$, is stated as the limit of $T\,C_{T,R}$ for exposures much longer than the coherence time. The far-field form (10) is a hypothesis, as in the paper, which quotes it from the generalised van Cittert - Zernike theorem under the quasi-homogeneous and far-field conditions. Frequencies are positive and $\lambda=c/\nu$ inside the frequency integral.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c006; Section 3, eqs. (9)-(11), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem vcz2_theorem_far_field {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (U : ℝ × ℝ → Omega → ℂ) (hU : IsCircularGaussian P U)
    (hmeas : ∀ x : ℝ, Measurable (fun p : ℝ × Omega => U (x, p.1) p.2))
    (W : ℝ → ℝ → ℝ → ℂ) (hW : IsCrossSpectralDensity P U W)
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (hS0 : ∀ x ν, 0 ≤ S0 x ν) (hg0 : ∀ ν, g0 0 ν = 1)
    (hfar : ∀ x1 x2 ν : ℝ, 0 < ν → W x1 x2 ν = farFieldCSD c R S0 g0 x1 x2 ν)
    (hfreq : ∀ x1 x2 ν : ℝ, ν ≤ 0 → W x1 x2 ν = 0)
    (x1 x2 : ℝ) (hW2 : MemLp (W x1 x2) 2) :
    Tendsto (fun T : ℝ => T * intensityAutocov P U T x1 x2) atTop
      (𝓝 (∫ ν in Set.Ioi (0 : ℝ),
        ‖ft (fun y => (S0 y ν : ℂ)) ((x1 - x2) / (wavelength c ν * R))‖ ^ 2 *
          ‖ft (fun y => g0 y ν) ((x1 + x2) / (2 * wavelength c ν * R))‖ ^ 2 /
            (wavelength c ν ^ 2 * R ^ 2))) := by sorry

end Arxiv1706_02824
