-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_not_rayleigh
-- name    : Arxiv1906_02603.burr_not_rayleigh
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:46:31.878299+00:00
-- url     : https://prove2.me/theorems/77c41941-a58a-428b-9917-255e3cbb8739
-- title:
--   Section I: the model histogram is not equal to the Rayleigh distribution
-- statement:
--   Let $\lambda>0$, $b>1$ and $S>0$. The model density of eq. (10) is not the Rayleigh density $R[A]=\frac{A}{S^2}e^{-A^2/(2S^2)}$ of eq. (15): there is $A>0$ with
--
--   $$N_n[A]\neq R[A].$$
--
--   **Formalization Note** The paper says its model histogram "somewhat resembles – but is not equal to – the Rayleigh distribution". Only "not equal" is formalized; "resembles" has no precise content in the paper.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c021; Section I Introduction, PDF p. 5; Rayleigh density eq. (15), PDF p. 16

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_not_rayleigh (lam b S : ℝ) (hlam : 0 < lam) (hb : 1 < b) (hS : 0 < S) :
    ∃ A : ℝ, 0 < A ∧ burrPdf lam b A ≠ rayleighPdf S A := by sorry

end Arxiv1906_02603
