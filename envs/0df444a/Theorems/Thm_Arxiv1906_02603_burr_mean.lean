-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_mean
-- name    : Arxiv1906_02603.burr_mean
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:44:00.373465+00:00
-- url     : https://prove2.me/theorems/68e0f2ff-9009-583e-a2a8-7c4444fc5d7e
-- title:
--   Eq. (11): the mean of the normalized histogram
-- statement:
--   Let $\lambda>0$ and $b>3/2$. The density of eq. (10) has a finite mean, and
--
--   $$\langle A\rangle=\int_0^\infty A\,N_n[A]\,dA=\frac{\lambda(-1+b)\sqrt\pi\,\Gamma(-\tfrac32+b)}{2\Gamma(b)}\qquad(\text{eq. }(11)).$$
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c006; Section II, eq. (11), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_mean (lam b : ℝ) (hlam : 0 < lam) (hb : 3 / 2 < b) :
    IntegrableOn (fun A : ℝ => A ^ 1 * burrPdf lam b A) (Ioi 0) ∧
    burrMoment lam b 1 =
      lam * (-1 + b) * Real.sqrt Real.pi * Real.Gamma (-3 / 2 + b) / (2 * Real.Gamma b) := by sorry

end Arxiv1906_02603
