-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq17_factorized_source_spectrum
-- name    : Arxiv1706_02824.eq17_factorized_source_spectrum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:12:31.673657+00:00
-- url     : https://prove2.me/theorems/890a1379-4d40-4727-9eb2-73bcab353434
-- title:
--   Eq. (17) (as proved): noise power spectrum for a factorised source spectral density
-- statement:
--   Under the hypotheses of eq. (16), suppose the source spectral density factorises, $S_0(x',\nu)=I_0(x')s(\nu)$ for $\nu>0$. Then $\Gamma_0(x',\nu)=\Gamma_0(x')s^2(\nu)$ with $\Gamma_0(x')=\int I_0(y')I_0(x'+y')\,dy'$, and
--   $$W_{T,R,x}(\xi)=|\hat P(\xi)|^2\,T^{-1}\int_0^\infty\Gamma_0(\lambda R\xi)\,\frac{1}{\lambda R}\Big|\hat g_0\Big(\frac{x}{\lambda R},\nu\Big)\Big|^2s^2(\nu)\,d\nu,\qquad\lambda=c/\nu .$$
--
--   **Formalization Note** This is the form the derivation establishes. The printed eq. (17) places $\Gamma_0(\lambda R\xi)$ outside the frequency integral. Since $\lambda=c/\nu$ varies over the spectrum, that is valid only when $\lambda$ can be treated as constant (quasi-monochromatic light); inside the integral the factor is kept.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c011; Section 4, eq. (17) and the sentence before it, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq17_factorized_source_spectrum (c R T : ℝ) (hc : 0 < c) (hR : 0 < R) (hT : 0 < T)
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
    (ξ : ℝ)
    (I0 s : ℝ → ℝ) (hfac : ∀ y ν : ℝ, 0 < ν → S0 y ν = I0 y * s ν) :
    (∀ ν : ℝ, 0 < ν → ∀ x' : ℝ, autocorr (fun y => S0 y ν) x' = autocorr I0 x' * s ν ^ 2) ∧
    noisePowerSpectrum c R T S0 g0 Pf x ξ =
      ((‖ft (fun y => (Pf y : ℂ)) ξ‖ ^ 2 * T⁻¹ *
        ∫ ν in Set.Ioi (0 : ℝ), autocorr I0 (wavelength c ν * R * ξ) * (1 / (wavelength c ν * R)) *
          ‖ft (fun y => g0 y ν) (x / (wavelength c ν * R))‖ ^ 2 * s ν ^ 2 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
