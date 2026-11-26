-- Prove2me | Theorems.Thm_Arxiv2005_04287_intensity_pdf_lomax
-- name    : Arxiv2005_04287.intensity_pdf_lomax
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:10:26.053904+00:00
-- url     : https://prove2.me/theorems/52e8f5a0-d78f-5eb6-957b-fc23eb1ece4c
-- title:
--   Eqs. (13)-(14): the echo intensity is Lomax distributed
-- statement:
--   Let $b>1$, $a_{\min}>0$ and $I_0>0$. Let the vessel radius $a$ have the power-law density of eq. (7), and let the echo intensity be $I=I_0(a-a_{\min})$ for $a>a_{\min}$ ($0$ otherwise). Then $I$ has the density (eq. (13))
--
--   $$p_I(I)=\frac{b-1}{a_{\min}^{1-b}\,I_0\big(\tfrac{I}{I_0}+a_{\min}\big)^b},\qquad I>0.$$
--
--   With $\lambda_2=I_0a_{\min}$ this equals (eq. (14))
--
--   $$p_I(I)=\frac{(b-1)\lambda_2^{\,b-1}}{(I+\lambda_2)^b},$$
--
--   the Lomax (Pareto type II) density with shape $b-1$ and scale $\lambda_2$.
--
--   **Formalization Note** The law of $I$ is the push-forward of the radius law under the intensity map. The Lomax identification is the pointwise identity of (14) with the standard density $\frac{\alpha}{s}(1+x/s)^{-(\alpha+1)}$, $\alpha=b-1$, $s=\lambda_2$.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c003; Theory, 'Probability of Intensity', eqs. (11)-(14), PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem intensity_pdf_lomax (b amin I0 : ℝ) (hb : 1 < b) (hamin : 0 < amin) (hI0 : 0 < I0) :
    (powerLawMeasure b amin).map (intensityMap I0 amin) =
      volume.withDensity (fun I => ENNReal.ofReal (intensityDensity13 b amin I0 I)) ∧
    (∀ I : ℝ, intensityDensity13 b amin I0 I = intensityDensity14 b (I0 * amin) I) ∧
    (∀ I : ℝ, intensityDensity14 b (I0 * amin) I = lomaxDensity (b - 1) (I0 * amin) I) := by sorry

end Arxiv2005_04287
