-- Prove2me | Theorems.Thm_Arxiv1906_02603_histogram_normalization
-- name    : Arxiv1906_02603.histogram_normalization
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:42:11.843428+00:00
-- url     : https://prove2.me/theorems/ac5ee041-2fa7-4404-9475-1ab19992752c
-- title:
--   Eq. (9): the integral of the histogram and the normalized density
-- statement:
--   Let $N_0>0$, $A_0>0$, $a_{\min}>0$ and $b>1$. The histogram $N[A]$ of eq. (8) is integrable on $(0,\infty)$ with
--
--   $$\int_0^\infty N[A]\,dA=\frac{N_0}{(b-1)a_{\min}^{b-1}},$$
--
--   and dividing by this integral gives the density of eq. (9),
--
--   $$N_n[A]=\frac{2A\,a_{\min}^{b-1}(b-1)}{A_0^2\big[(A/A_0)^2+a_{\min}\big]^b},\qquad\int_0^\infty N_n[A]\,dA=1.$$
--
--   **Formalization Note** The paper does not state $b>1$ and $a_{\min}>0$ here; the integral is finite only under these conditions, and integrability is stated explicitly.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c004; Section II, normalization integral and eq. (9), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem histogram_normalization (N0 A0 amin b : ℝ) (hN0 : 0 < N0) (hA0 : 0 < A0)
    (hamin : 0 < amin) (hb : 1 < b) :
    IntegrableOn (ampHist N0 A0 amin b) (Ioi 0) ∧
    ∫ A in Ioi (0 : ℝ), ampHist N0 A0 amin b A = N0 / ((b - 1) * amin ^ (b - 1)) ∧
    (∀ A : ℝ, normHist A0 amin b A = ampHist N0 A0 amin b A / (N0 / ((b - 1) * amin ^ (b - 1)))) ∧
    ∫ A in Ioi (0 : ℝ), normHist A0 amin b A = 1 := by sorry

end Arxiv1906_02603
