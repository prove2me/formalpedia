-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_log_term_antitone
-- name    : BOPDistrib.Misalign.log_term_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:21.31841+00:00
-- url     : https://prove2.me/theorems/c7895fef-3887-4cd4-aa3c-c5f1b36a98e4
-- title:
--   Proof of Proposition 2, p. 47 (PDF 48) — the term (1−β)/α·ln((1−βe^{−α(v_h−m)})/(1−β)) decreases in α with range [0, β(v_h−m)]
-- statement:
--   Let $0<\beta<1$ and $m\le v_h$. For $\alpha>0$ put
--   $$T(\alpha)=\frac{1-\beta}{\alpha}\ln\frac{1-\beta e^{-\alpha(v_h-m)}}{1-\beta}.$$
--   Then:
--   1. $T$ is non-increasing on $(0,\infty)$;
--   2. $0\le T(\alpha)\le\beta(v_h-m)$ for every $\alpha>0$;
--   3. $T(\alpha)\to\beta(v_h-m)$ as $\alpha\to0^+$, and $T(\alpha)\to0$ as $\alpha\to\infty$.
--
--   The term $T$ is $(1-\beta)$ times the log term of the minimum refund $r_\alpha(m)$. Its monotonicity in $\alpha$ is the basis of every risk-aversion threshold of the strategy map ($a_1,\dots,a_4$, $a^{cs}_F$).
--
--   **Formalization Note** The page says "has range $[0,\beta(v_h-m)]$". This is stated as the two-sided bound together with the two limits at the ends of $(0,\infty)$.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 47 (PDF 48), proof of Proposition 2

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Proof of Proposition 2 (p. 47): for `m ≤ v_h` and `0 < β < 1`, the term
`(1 − β)/α · ln((1 − β e^{−α(v_h − m)})/(1 − β))` is antitone in `α > 0`, takes values in
`[0, β(v_h − m)]`, tends to `β(v_h − m)` as `α → 0⁺` and to `0` as `α → ∞`. -/
theorem log_term_antitone (P : Params) (m : ℝ) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hm : m ≤ P.vh) :
    AntitoneOn (fun α => (1 - P.β) * logTerm P m α) (Set.Ioi 0) ∧
      (∀ α : ℝ, 0 < α →
        0 ≤ (1 - P.β) * logTerm P m α ∧ (1 - P.β) * logTerm P m α ≤ P.β * (P.vh - m)) ∧
      Filter.Tendsto (fun α => (1 - P.β) * logTerm P m α) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (P.β * (P.vh - m))) ∧
      Filter.Tendsto (fun α => (1 - P.β) * logTerm P m α) Filter.atTop (nhds 0) := by sorry

end BOPDistrib.Misalign
