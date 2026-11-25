-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_cdf
-- name    : Arxiv1906_02603.burr_cdf
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:43:33.252238+00:00
-- url     : https://prove2.me/theorems/c33b8470-3198-4935-8085-facee233a935
-- title:
--   Eq. (14): the cumulative distribution function of the Burr density
-- statement:
--   Let $\lambda>0$ and $b>1$. For every $A\ge0$, the cumulative distribution function of the density of eq. (10) is
--
--   $$\int_0^AN_n[x]\,dx=1-\Big[1+\Big(\frac A\lambda\Big)^2\Big]^{-(b-1)}\qquad(\text{eq. }(14)).$$
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c012; Section IV, eq. (14), PDF p. 15

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_cdf (lam b : ℝ) (hlam : 0 < lam) (hb : 1 < b) (A : ℝ) (hA : 0 ≤ A) :
    ∫ x in (0 : ℝ)..A, burrPdf lam b x = burrCdf lam b A := by sorry

end Arxiv1906_02603
