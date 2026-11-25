-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_mean_square
-- name    : Arxiv1906_02603.burr_mean_square
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:44:46.696657+00:00
-- url     : https://prove2.me/theorems/f1541b9b-d5d1-4a4b-9d43-49a8f4d4d61c
-- title:
--   Eq. (12): the mean square of the normalized histogram
-- statement:
--   Let $\lambda>0$ and $b>2$. The density of eq. (10) has a finite second moment, and
--
--   $$\langle A^2\rangle=\int_0^\infty A^2N_n[A]\,dA=\frac{\lambda^2}{b-2}\qquad(\text{eq. }(12)).$$
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c007; Section II, eq. (12), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_mean_square (lam b : ℝ) (hlam : 0 < lam) (hb : 2 < b) :
    IntegrableOn (fun A : ℝ => A ^ 2 * burrPdf lam b A) (Ioi 0) ∧
    burrMoment lam b 2 = lam ^ 2 / (b - 2) := by sorry

end Arxiv1906_02603
