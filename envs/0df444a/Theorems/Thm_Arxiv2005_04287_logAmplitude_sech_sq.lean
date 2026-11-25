-- Prove2me | Theorems.Thm_Arxiv2005_04287_logAmplitude_sech_sq
-- name    : Arxiv2005_04287.logAmplitude_sech_sq
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:11:31.210885+00:00
-- url     : https://prove2.me/theorems/7a32252e-904d-486e-b454-8e097300bfa4
-- title:
--   Eq. (15), p. 10: for $\lambda=1$, $b=2$ the log-amplitude density is the sech$^2$ density
-- statement:
--   For $\lambda=1$ and $b=2$, the log-amplitude density of eq. (15) is the sech$^2$ density: for every real $y$,
--
--   $$p_y(y)=\frac{2e^{2y}}{(e^{2y}+1)^2}=\tfrac12\,\mathrm{sech}^2(y).$$
--
--   **Formalization Note** The sech$^2$ density is written $1/(2\cosh^2 y)$.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c005; Theory, 'Probability of Log-Transformed Envelope', text after eq. (15), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem logAmplitude_sech_sq (y : ℝ) :
    logAmpDensity 2 1 y = 1 / (2 * Real.cosh y ^ 2) := by sorry

end Arxiv2005_04287
