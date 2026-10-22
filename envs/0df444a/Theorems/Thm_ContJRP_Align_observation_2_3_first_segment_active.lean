-- Prove2me | Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active
-- name    : ContJRP.Align.observation_2_3_first_segment_active
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:32.761955+00:00
-- url     : https://prove2.me/theorems/a160a678-f538-4f9c-93e9-53b9dc3306f2
-- title:
--   Observation 2.3, p. 8 — S_1 is active, so R*_1 ∈ R*
-- statement:
--   Let $\epsilon\in(0,\tfrac12)$, let $T^*$ be a policy with $n\ge1$ and all $T^*_i>0$, and let $\tilde T_{\min}$ satisfy (2), $(1-\epsilon/2)T^*_{\min}\le\tilde T_{\min}\le T^*_{\min}$. Then the first segment
--   $$S_1=[\tilde T_{\min},(1+\epsilon)\tilde T_{\min})$$
--   is active, i.e. $1\in\mathcal A^*$; hence its representative $R^*_1$ belongs to $\mathcal R^*$.
--
--   This guarantees that the large-interval option $\lceil T^{\max}_i\rceil^{(\hat R_1)}$ of the final policy is a multiple of an approximate representative, so it falls on placed joint orders.
--
--   **Formalization Note** In Lean the paper's $S_1$ is segment index $0$, so the statement is `0 ∈ active ε Tt Tstar`; it includes $1\le L$.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 8, Observation 2.3

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem observation_2_3_first_segment_active (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar) :
    0 ∈ active ε Tt Tstar := by sorry

end ContJRP.Align
