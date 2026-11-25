-- Prove2me | Theorems.Thm_Arxiv2005_04287_logAmplitude_pdf
-- name    : Arxiv2005_04287.logAmplitude_pdf
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:10:46.5088+00:00
-- url     : https://prove2.me/theorems/5f8f8928-d2a5-59f0-95b8-3d3178efec23
-- title:
--   Eq. (15): the density of the log amplitude $y=\ln A$ (as proved: on all real $y$)
-- statement:
--   Let $b>1$ and $\lambda>0$, and let the amplitude $A$ have the Burr density of eq. (10). Then $y=\ln A$ has the density
--
--   $$p_y(y)=\frac{2(b-1)\exp[2y]}{\lambda^2\Big(\frac{\exp[2y]}{\lambda^2}+1\Big)^b},\qquad y\in\mathbb{R}.$$
--
--   **Formalization Note** The paper prints the range as "$y>0$ and $b>1$". The change of variables $A=e^y$ maps $A\in(0,\infty)$ onto all of $\mathbb{R}$, and the formula integrates to $1$ over $\mathbb{R}$ but not over $y>0$ (for $\lambda=1$, $b=3$ the integral over $y>0$ is $1/4$). The statement is therefore made on all of $\mathbb{R}$, which is what the derivation establishes.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c004; Theory, 'Probability of Log-Transformed Envelope', eq. (15), PDF pp. 9-10; Table 1 row 3, PDF p. 13

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem logAmplitude_pdf (b lam : ℝ) (hb : 1 < b) (hlam : 0 < lam) :
    (burrMeasure b lam).map Real.log = logAmpMeasure b lam := by sorry

end Arxiv2005_04287
