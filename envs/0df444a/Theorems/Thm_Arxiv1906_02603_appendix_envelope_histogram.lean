-- Prove2me | Theorems.Thm_Arxiv1906_02603_appendix_envelope_histogram
-- name    : Arxiv1906_02603.appendix_envelope_histogram
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:47:01.143456+00:00
-- url     : https://prove2.me/theorems/8ec009b9-79b2-5bab-b500-ad1d2bf36369
-- title:
--   Appendix, eq. (16) example: the histogram of the envelope $A_1(1-x^2)$ and its singularity at the maximum
-- statement:
--   Let $A_1>0$, and sample the envelope $y=g(x)=A_1(1-x^2)$ uniformly in $x\in(0,1)$. Then:
--
--   1. $|dy/dx|=A_1\cdot2x$ for $0<x<1$;
--   2. for $0<y<A_1$, $x=g^{-1}(y)=\sqrt{1-y/A_1}$ lies in $(0,1)$ and $g(g^{-1}(y))=y$;
--   3. the law of $y$ (the image of Lebesgue measure on $(0,1)$ under $g$) has density on $(0,A_1)$
--
--   $$f(y)=\frac{1}{2A_1\sqrt{1-y/A_1}};$$
--
--   4. $f(y)\to+\infty$ as $y\to A_1^-$: the histogram is singular at the local maximum $A_1$ of the envelope.
--
--   **Formalization Note** The paper writes that the singularity is "as $y\to1$"; the value of the local maximum is $A_1$ (equal to $1$ only in its Fig. 13). The transformation rule (16) is stated as an identity of measures in item 3.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c016; Appendix, eq. (16) and the example after it, Fig. 13, PDF pp. 20-21

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem appendix_envelope_histogram (A1 : ℝ) (hA1 : 0 < A1) :
    (∀ x ∈ Ioo (0 : ℝ) 1, |deriv (appendixEnvelope A1) x| = A1 * (2 * x)) ∧
    (∀ y ∈ Ioo (0 : ℝ) A1, Real.sqrt (1 - y / A1) ∈ Ioo (0 : ℝ) 1 ∧
      appendixEnvelope A1 (Real.sqrt (1 - y / A1)) = y) ∧
    Measure.map (appendixEnvelope A1) (volume.restrict (Ioo (0 : ℝ) 1)) =
      (volume.restrict (Ioo (0 : ℝ) A1)).withDensity (fun y => ENNReal.ofReal (appendixHist A1 y)) ∧
    Tendsto (appendixHist A1) (𝓝[<] A1) atTop := by sorry

end Arxiv1906_02603
