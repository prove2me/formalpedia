-- Prove2me | Theorems.Thm_Arxiv2005_04287_amplitude_pdf_burr
-- name    : Arxiv2005_04287.amplitude_pdf_burr
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:09:08.162608+00:00
-- url     : https://prove2.me/theorems/df30744d-2829-5665-9968-49d2bdf94849
-- title:
--   Eqs. (9)-(10): the echo amplitude is Burr XII distributed
-- statement:
--   Let $b>1$, $a_{\min}>0$ and $A_0>0$. Let the vessel radius $a$ have the power-law density of eq. (7),
--
--   $$p(a)=\frac{b-1}{a_{\min}}\Big(\frac{a}{a_{\min}}\Big)^{-b}\quad(a>a_{\min}),$$
--
--   and let the echo amplitude be $A=A_0\sqrt{a-a_{\min}}$ for $a>a_{\min}$ ($0$ otherwise). Then $A$ has the density (eq. (9))
--
--   $$p[A]=\frac{2A\,a_{\min}^{\,b-1}(b-1)}{A_0^2\Big[\big(\tfrac{A}{A_0}\big)^2+a_{\min}\Big]^b},\qquad A>0.$$
--
--   With $\lambda=A_0\sqrt{a_{\min}}$ this equals the two-parameter density (eq. (10))
--
--   $$p[A]=\frac{2A(b-1)}{\lambda^2\Big[\big(\tfrac{A}{\lambda}\big)^2+1\Big]^b},$$
--
--   which is the Burr Type XII density with $c=2$, $k=b-1$ and scale $\lambda$.
--
--   **Formalization Note** The law of $A$ is the push-forward of the radius law under the amplitude map, and the claim is that it equals the measure with density (9) on $\mathbb{R}$, which is $0$ for $A\le0$. The Burr XII identification is the pointwise identity of (10) with the standard density $\frac{ck}{\lambda}(x/\lambda)^{c-1}(1+(x/\lambda)^c)^{-(k+1)}$.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c001; Theory, 'Probability of Amplitudes', eqs. (7)-(10), PDF pp. 7-8

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem amplitude_pdf_burr (b amin A0 : ℝ) (hb : 1 < b) (hamin : 0 < amin) (hA0 : 0 < A0) :
    (powerLawMeasure b amin).map (ampMap A0 amin) =
      volume.withDensity (fun A => ENNReal.ofReal (ampDensity9 b amin A0 A)) ∧
    (∀ A : ℝ, ampDensity9 b amin A0 A = burrDensity b (A0 * Real.sqrt amin) A) ∧
    (∀ A : ℝ, burrDensity b (A0 * Real.sqrt amin) A =
      burrXIIDensity 2 (b - 1) (A0 * Real.sqrt amin) A) := by sorry

end Arxiv2005_04287
