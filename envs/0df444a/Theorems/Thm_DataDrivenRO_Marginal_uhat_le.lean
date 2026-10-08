-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_uhat_le
-- name    : DataDrivenRO.Marginal.uhat_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:22:02.535693+00:00
-- url     : https://prove2.me/theorems/bb4ba329-2ce1-4fbd-86aa-268570fd592f
-- title:
--   p. 21 — if N − s + 1 < s then û^(N−s+1)_i ≤ û^(s)_i
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, let $\hat{\mathbf u}^{(0)}\le\hat{\mathbf u}^{(N+1)}$ be the a priori box ends, and let $s$ be the index of (26). If $N-s+1<s$, then for every sample $\hat{\mathbf u}^1,\dots,\hat{\mathbf u}^N\in\mathbb R^d$ and every coordinate $i$,
--   $$\hat u^{(N-s+1)}_i\le\hat u^{(s)}_i .$$
--
--   It makes the two-sided box $\mathcal U^M_\epsilon$ of (28) nonempty and is what turns the sum in (EC.8) into the maximum form (29).
--
--   **Formalization Note** If $s=N+1$ the two sides are the box ends $\hat u^{(0)}_i$ and $\hat u^{(N+1)}_i$; otherwise both are order statistics of the sample. The statement holds for every sample, with no measure involved.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §6, p. 21 (sentence ending the second paragraph); EC.1.5, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- p. 21: if `N − s + 1 < s` then `û^(N−s+1)_i ≤ û^(s)_i` for every sample and every `i`. -/
theorem uhat_le {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (i : Fin d) :
    uhat S lo hi i (N + 1 - sIndex N d ε α) ≤ uhat S lo hi i (sIndex N d ε α) := by sorry

end DataDrivenRO.Marginal
