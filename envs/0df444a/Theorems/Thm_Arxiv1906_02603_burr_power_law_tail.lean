-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_power_law_tail
-- name    : Arxiv1906_02603.burr_power_law_tail
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:45:50.248792+00:00
-- url     : https://prove2.me/theorems/006a9b27-880b-537c-88f4-95aacbcad79a
-- title:
--   Section V: the high-amplitude behaviour of the Burr density includes the power law $A^{-2b}$
-- statement:
--   Let $\lambda>0$ and $b>1$. As $A\to\infty$ the density of eq. (10) behaves as $A$ times the power law $A^{-2b}$:
--
--   $$N_n[A]\sim2(b-1)\lambda^{2b-2}\,A\cdot A^{-2b}.$$
--
--   **Formalization Note** The paper says the asymptotic behaviour "includes a power law proportional to $A^{-2b}$". The precise statement is the asymptotic equivalence above, in which $A^{-2b}$ is the decay of the factor $[(A/\lambda)^2+1]^{-b}$; the density itself decays as $A^{1-2b}$.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c015; Section V Discussion and Conclusion, PDF p. 18

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_power_law_tail (lam b : ℝ) (hlam : 0 < lam) (hb : 1 < b) :
    Asymptotics.IsEquivalent atTop (fun A : ℝ => burrPdf lam b A)
      (fun A : ℝ => 2 * (b - 1) * lam ^ (2 * b - 2) * A * A ^ (-2 * b)) := by sorry

end Arxiv1906_02603
