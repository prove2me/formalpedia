-- Prove2me | Theorems.Thm_Arxiv1507_03491_window_conditions
-- name    : Arxiv1507_03491.window_conditions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:15:51.259727+00:00
-- url     : https://prove2.me/theorems/b7115558-65cc-424b-aa52-b272865803c3
-- title:
--   Eqs. (2.8)–(2.9): the bump window satisfies the window conditions once $M_0>4$
-- statement:
--   Let $M_0>4$ and let $W=W_{M_0}$ be the bump window of eq. (2.9). Then $W\in C^\infty(\mathbb R)$, its support is contained in $\Gamma_0=(-M_0,M_0)$, and
--
--   $$W(x)=\begin{cases}0,& x\le-\tfrac34M_0,\\ 1,& -\tfrac14M_0\le x\le\tfrac14M_0,\\ 0,& x\ge\tfrac34M_0,\end{cases}$$
--
--   which are the window conditions (2.8).
--
--   This is the window that the hybrid representation uses to isolate the nearly singular part of the layer-potential density.
--
--   **Formalization Note** The paper's $3/4M_0$ and $1/4M_0$ are read as $\tfrac34M_0$ and $\tfrac14M_0$. "Supported in $\Gamma_0$" is stated for the closed support.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c001; Section 2, eqs. (2.8)–(2.9) and the sentence after (2.9), PDF pp. 6–7

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem window_conditions (M0 : ℝ) (hM0 : 4 < M0) :
    ContDiff ℝ ∞ (window M0) ∧ tsupport (window M0) ⊆ Ioo (-M0) M0 ∧
    (∀ x : ℝ, x ≤ -(3 / 4 * M0) → window M0 x = 0) ∧
    (∀ x : ℝ, -(1 / 4 * M0) ≤ x → x ≤ 1 / 4 * M0 → window M0 x = 1) ∧
    (∀ x : ℝ, 3 / 4 * M0 ≤ x → window M0 x = 0) := by sorry

end Arxiv1507_03491
