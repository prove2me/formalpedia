-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq16_noise_power_spectrum
-- name    : Arxiv1706_02824.eq16_noise_power_spectrum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:08:55.9672+00:00
-- url     : https://prove2.me/theorems/ea1ef7d7-0d02-4e9a-ade8-34c214c833fc
-- title:
--   Eq. (16): noise power spectrum of flat-field images
-- statement:
--   Let $c,R,T>0$ and $\lambda=c/\nu$. Let $S_0(\cdot,\nu)\ge0$ be integrable and square-integrable with $\hat S_0(0,\nu)\ne0$ for $\nu>0$, and let $g_0(0,\nu)=1$. Let the detector PSF $P\ge0$ be integrable with $\int P=1$, and let $P_2(x)=\int P(x+y)P(y)\,dy$. Fix the centre $x$ of a stationary patch. The filtered autocovariance on the patch, as a function of $r=x_1-x_2$, is (eq. 15)
--   $$r\mapsto T^{-1}\int_0^\infty\sigma^2(x,\nu)\,\frac{(H*P_2)(r,\nu)}{H(0,\nu)}\,d\nu .$$
--   Assume this integrand is integrable jointly in $(r,\nu)$. Then the noise power spectrum $W_{T,R,x}(\xi)$, its Fourier transform in $r$, is
--   $$W_{T,R,x}(\xi)=|\hat P(\xi)|^2\,T^{-1}\int_0^\infty\frac{1}{\lambda R}\Big|\hat g_0\Big(\frac{x}{\lambda R},\nu\Big)\Big|^2\,\Gamma_0(\lambda R\xi,\nu)\,d\nu,\qquad \Gamma_0(x',\nu)=\int S_0(y',\nu)S_0(x'+y',\nu)\,dy'.$$
--
--   The flat-field noise power spectrum is thus the squared MTF $|\hat P|^2$ times a spectral average of the autocorrelation of the source spectral density.
--
--   **Formalization Note** The "stationary patch" is made explicit by freezing the mean coordinate at $x$ in the last line of eq. (15). The step from (15) to (16) is then exact, and the statement asserts equality. Joint integrability in $(r,\nu)$, used to exchange the Fourier transform with the frequency integral, is a regularity assumption the paper leaves implicit.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c010; Section 4, eqs. (13), (15) and (16), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq16_noise_power_spectrum (c R T : ℝ) (hc : 0 < c) (hR : 0 < R) (hT : 0 < T)
    (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (hS0 : ∀ x ν, 0 ≤ S0 x ν) (hg0 : ∀ ν, g0 0 ν = 1)
    (hS0int : ∀ ν : ℝ, 0 < ν → Integrable (fun y => S0 y ν))
    (hS0L2 : ∀ ν : ℝ, 0 < ν → MemLp (fun y => S0 y ν) 2)
    (hH0 : ∀ ν : ℝ, 0 < ν → ft (fun y => (S0 y ν : ℂ)) 0 ≠ 0)
    (Pf : ℝ → ℝ) (hP : ∀ y, 0 ≤ Pf y) (hPint : Integrable Pf) (hP1 : ∫ y : ℝ, Pf y = 1)
    (x : ℝ)
    (hjoint : Integrable (fun q : ℝ × ℝ => noiseVariance c R S0 g0 x q.2 *
        conv (fun r => noiseCorrelation c R S0 r q.2) (autocorr Pf) q.1 /
          noiseCorrelation c R S0 0 q.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))
    (ξ : ℝ) :
    noisePowerSpectrum c R T S0 g0 Pf x ξ =
      ((‖ft (fun y => (Pf y : ℂ)) ξ‖ ^ 2 * T⁻¹ *
        ∫ ν in Set.Ioi (0 : ℝ), 1 / (wavelength c ν * R) *
          ‖ft (fun y => g0 y ν) (x / (wavelength c ν * R))‖ ^ 2 *
            autocorr (fun y => S0 y ν) (wavelength c ν * R * ξ) : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
