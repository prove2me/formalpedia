-- Prove2me | Theorems.Thm_Arxiv2201_05558_psi_real_parts_pos
-- name    : Arxiv2201_05558.psi_real_parts_pos
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:07:58.632272+00:00
-- url     : https://prove2.me/theorems/7863145a-0e20-5cd3-b37b-719890478189
-- title:
--   Section 5.6 (Figure 5.1): the real parts of $\Psi_a,\Psi_b,\Psi_c,\Psi_d$ are positive
-- statement:
--   Let $w=e^{-i\pi/4}$ and let $\Psi_a(s)=\ln\cosh(ws)$, $\Psi_b(s)=\tanh(ws)/(ws)$, $\Psi_c(s)=2i\,[ws\tanh(ws)-1+\cosh(ws)^{-1}]/s^2$ and $\Psi_d(s)=1-\frac{3i}{s^3}\int_0^s[ws'\tanh(ws')-1+\cosh(ws')^{-1}]^2ds'$ be the functions of Proposition 5.4. For every $s>0$,
--
--   $$\operatorname{Re}\Psi_a(s)>0,\quad\operatorname{Re}\Psi_b(s)>0,\quad\operatorname{Re}\Psi_c(s)>0,\quad\operatorname{Re}\Psi_d(s)>0.$$
--
--   The real parts of $b_\Omega,c_\Omega,d_\Omega$ control the Gaussian decay of $\hat A_s$ in (5.38).
--
--   **Formalization Note** The paper states positivity next to a plot and gives no range. The statement is for $s>0$: $\Psi_a(0)=0$ is not positive, and $\Psi_{b,c,d}$ are undefined at $s=0$.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c012; Section 5.6, remark after Proposition 5.4 and Figure 5.1, PDF p. 21

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem psi_real_parts_pos (s : ℝ) (hs : 0 < s) :
    0 < (psiA 0 s).re ∧ 0 < (psiB 0 s).re ∧ 0 < (psiC 0 s).re ∧ 0 < (psiD 0 s).re := by sorry

end Arxiv2201_05558
