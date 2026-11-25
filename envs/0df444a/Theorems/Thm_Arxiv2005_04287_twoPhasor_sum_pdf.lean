-- Prove2me | Theorems.Thm_Arxiv2005_04287_twoPhasor_sum_pdf
-- name    : Arxiv2005_04287.twoPhasor_sum_pdf
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:12:42.166204+00:00
-- url     : https://prove2.me/theorems/fee959df-3a46-4c1a-be98-a079ccef492b
-- title:
--   Eq. (18): density of the sum of two in-phase components at $b=2.5$ (as proved: constant $4/\pi$)
-- statement:
--   Let $Z_A$ and $Z_B$ be independent, each with the density of eq. (17) at $b=2.5$ (and $\lambda=1$), which is $\frac{2}{\pi}(1+x^2)^{-2}$. Then $Z_C=Z_A+Z_B$ has the density
--
--   $$p(Z_C)=\frac{4}{\pi}\,\frac{20+Z_C^2}{(4+Z_C^2)^3}=\frac4\pi\left(\frac{20}{(4+Z_C^2)^3}+\frac{Z_C^2}{(4+Z_C^2)^3}\right),\qquad Z_C\in\mathbb{R}.$$
--
--   **Formalization Note** The paper prints the prefactor as $4\pi$, and with it the function integrates to $\pi^2$, not $1$. The convolution of two copies of eq. (17) at $b=2.5$ gives the prefactor $4/\pi$, and the statement uses $4/\pi$. The paper's "$Z_C=Z_A+Z_C$" is read as $Z_A+Z_B$.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c007; Theory, 'Increasing Power Law b with Complex Summation', eq. (18), PDF p. 12; Table 1 row 5, PDF p. 13

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem twoPhasor_sum_pdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (hXlaw : P.map X = pearsonMeasure (5 / 2)) (hYlaw : P.map Y = pearsonMeasure (5 / 2)) :
    P.map (fun ω => X ω + Y ω) =
      volume.withDensity (fun z => ENNReal.ofReal (4 / Real.pi * (20 + z ^ 2) / (4 + z ^ 2) ^ 3)) := by sorry

end Arxiv2005_04287
