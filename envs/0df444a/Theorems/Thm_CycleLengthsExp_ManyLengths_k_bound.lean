-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_k_bound
-- name    : CycleLengthsExp.ManyLengths.k_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:37.627054+00:00
-- url     : https://prove2.me/theorems/d92ae2e8-db36-4f12-874d-170104fdea9f
-- title:
--   Theorem 2 proof — the chosen k is O(log(1/α)/α)
-- statement:
--   Set $k(\alpha)=2\lceil\log_2(3/\alpha)/\log_2(1+\alpha/2)\rceil+1$. There is one absolute constant $K>0$ such that, for every $0<\alpha\le1$,
--   $$k(\alpha)\le K\,\frac{\log_2(2/\alpha)}{\alpha}.$$
--
--   This uniform estimate converts the explicit integer chosen in the proof into the dependence on $\alpha$ stated by Theorem 2.
--
--   **Formalization Note** The paper writes $O(\log(1/\alpha)/\alpha)$. The shifted logarithm $\log_2(2/\alpha)$ supplies the positive endpoint value at $\alpha=1$; for $\alpha\le1/2$ it differs only by an absolute factor. The constant $K$ is quantified before $\alpha$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 13, proof of Theorem 2, displayed definition of k

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- The `O(log(1/α)/α)` bound following the displayed definition of `k`, p. 13. -/
theorem k_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      (kNum α : ℝ) ≤ K * Real.logb 2 (2 / α) / α := by sorry

end CycleLengthsExp.ManyLengths
