-- Prove2me | Theorems.Thm_BoundedNV_Pooling_scale_comparison
-- name    : BoundedNV.Pooling.scale_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:26.524731+00:00
-- url     : https://prove2.me/theorems/94ebbd6a-6d44-40b8-a591-ced337da42c8
-- title:
--   Proof of Proposition 7, p. 588 — comparison of canonical profit scales
-- statement:
--   For $0<c<p$, $\beta>0$, and two positive scales $s\leq s'$, let $E_s$ be the expectation of canonical profit $\Pi(z)$ under the logit density proportional to $e^{s\Pi(z)/\beta}$ on $\mathbb R$. Then
--
--   $$
--   E_s\leq E_{s'},\qquad E_s=E_{s'}\ \Longleftrightarrow\ s=s'.
--   $$
--
--   This is the scale comparison applied to each individual location and the pooled location in Proposition 7.
--
--   **Formalization Note** This statement specializes the paper's Proposition 5 to its canonical normal newsvendor. Both scales are positive and the same $\beta$ governs both logit laws.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 588 (PDF 23), proof of Proposition 7, paragraph after eq. (66); Proposition 5 proof p. 587 (PDF 22)

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical

namespace BoundedNV.Pooling

/-- Proof of Proposition 7, p. 588: scaling the canonical profit improves its logit mean,
with equality precisely when the scales agree. -/
theorem scale_comparison (p c β s s' : ℝ)
    (hc : 0 < c) (hcp : c < p) (hβ : 0 < β)
    (hs : 0 < s) (hss' : s ≤ s') :
    centeredExpectedProfit p c β s ≤ centeredExpectedProfit p c β s' ∧
      (centeredExpectedProfit p c β s = centeredExpectedProfit p c β s' ↔ s = s') := by sorry

end BoundedNV.Pooling
