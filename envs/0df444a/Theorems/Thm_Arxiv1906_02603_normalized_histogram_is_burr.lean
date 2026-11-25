-- Prove2me | Theorems.Thm_Arxiv1906_02603_normalized_histogram_is_burr
-- name    : Arxiv1906_02603.normalized_histogram_is_burr
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:42:54.490068+00:00
-- url     : https://prove2.me/theorems/c7209724-6fa5-430f-bef7-c07f4c889046
-- title:
--   Eq. (10): the normalized histogram is a Burr Type XII distribution with $c=2$
-- statement:
--   Let $A_0>0$, $a_{\min}>0$, $b>1$ and $\lambda=A_0\sqrt{a_{\min}}$. Then $\lambda>0$, the normalized histogram of eq. (9) equals
--
--   $$N_n[A]=\frac{2A(b-1)}{\lambda^2\big[(A/\lambda)^2+1\big]^b}\qquad(\text{eq. }(10)),$$
--
--   and for $A>0$ this is the Burr Type XII density with $c=2$, $k=b-1$ and scale $\lambda$:
--
--   $$N_n[A]=\frac{ck}{\lambda}\Big(\frac A\lambda\Big)^{c-1}\Big(1+\Big(\frac A\lambda\Big)^c\Big)^{-(k+1)}.$$
--
--   **Formalization Note** The paper names only $c=2$; the second shape parameter $k=b-1$ is read off from the formula (Rodriguez's parametrization).
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c005; Section II, eq. (10), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem normalized_histogram_is_burr (A0 amin b : ℝ) (hA0 : 0 < A0) (hamin : 0 < amin)
    (hb : 1 < b) :
    0 < burrScale A0 amin ∧
    (∀ A : ℝ, normHist A0 amin b A = burrPdf (burrScale A0 amin) b A) ∧
    (∀ A : ℝ, 0 < A → burrPdf (burrScale A0 amin) b A = burrXIIPdf 2 (b - 1) (burrScale A0 amin) A) := by sorry

end Arxiv1906_02603
