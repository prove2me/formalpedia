-- Prove2me | Theorems.Thm_Arxiv2610_39302_subsample_interval_scaling
-- name    : Arxiv2610_39302.subsample_interval_scaling
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:08:05.999072+00:00
-- url     : https://prove2.me/theorems/18559967-5333-4e53-8dd4-55d841ed43cf
-- title:
--   Appendix C: the spread of 800-pair subsets is $\sqrt{224/800}$ standard errors
-- statement:
--   Let $x_1,\dots,x_{1024}$ be per-pair scores on the 1,024 pairs of WIT-1024, with mean $\bar x$ and sample variance $s^2=\sum_i(x_i-\bar x)^2/1023$, so that the standard error of the full score is $s/\sqrt{1024}$. For a uniformly random subset $S$ of $800$ pairs drawn without replacement, let $\bar x_S$ be its mean. Then the spread of the subset scores around the full score is $\sqrt{224/800}$ times the full score's standard error:
--
--   $$\Big(E_S\,(\bar x_S-\bar x)^2\Big)^{1/2}=\sqrt{\frac{224}{800}}\cdot\frac{s}{\sqrt{1024}}.$$
--
--   This is the rescaling the paper uses to turn the spread of 800-pair subsets into an interval for the 1,024-pair score.
--
--   **Formalization Note** The paper states this "for average-like statistics"; the statement is the exact identity for an average of fixed per-pair scores. The mutual 10-NN score is not exactly such an average, and the paper's use of it there is approximate.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c052; Appendix C, 'Uncertainty on WIT', PDF p. 31

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem subsample_interval_scaling (x : Fin 1024 → ℝ) :
    subsampleSpread x 800 = Real.sqrt (224 / 800) * (Real.sqrt (sampleVar x) / Real.sqrt 1024) := by sorry

end Arxiv2610_39302
