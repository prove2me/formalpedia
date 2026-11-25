-- Prove2me | Theorems.Thm_Arxiv2005_04287_inPhase_pdf_pearson
-- name    : Arxiv2005_04287.inPhase_pdf_pearson
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:12:01.355467+00:00
-- url     : https://prove2.me/theorems/5e0d5542-5103-47c3-95d3-e086a60c46ad
-- title:
--   Eq. (17): the in-phase component $|A|\cos\theta_A$ has a double-sided Pearson density
-- statement:
--   Let $b>1$. Let $|A|$ have the Burr density of eq. (10) with $\lambda=1$, let $\theta_A$ be uniform on $[0,2\pi)$, and let $|A|$ and $\theta_A$ be independent. Then the in-phase component $\hat A=|A|\cos\theta_A$ has the double-sided Pearson density
--
--   $$p(\hat A)=\frac{(b-1)\,\Gamma\!\big(b-\tfrac12\big)}{\sqrt\pi\,\Gamma(b)\,\big(1+\hat A^2\big)^{b-\frac12}},\qquad \hat A\in\mathbb{R},$$
--
--   and $E[\hat A]=0$.
--
--   **Formalization Note** The mean of $\hat A$ exists exactly when $b>3/2$, because the density decays like $|\hat A|^{-(2b-1)}$. The claim $E[\hat A]=0$ is stated with integrability for $b>3/2$; for $1<b\le3/2$ the mean does not exist. The random variables live on an arbitrary probability space, $|A|$ is written $R$ and $\theta_A$ is written `th`.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c015; Theory, 'Increasing Power Law b with Complex Summation', eq. (17), PDF pp. 11-12; Table 1 row 4, PDF p. 13

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem inPhase_pdf_pearson {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 1 < b) (R th : Ω → ℝ) (hR : Measurable R) (hth : Measurable th)
    (hind : IndepFun R th P) (hRlaw : P.map R = burrMeasure b 1)
    (hthlaw : P.map th = uniformPhase) :
    P.map (fun ω => R ω * Real.cos (th ω)) = pearsonMeasure b ∧
    (3 / 2 < b → Integrable (fun ω => R ω * Real.cos (th ω)) P ∧
      ∫ ω, R ω * Real.cos (th ω) ∂P = 0) := by sorry

end Arxiv2005_04287
