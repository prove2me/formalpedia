-- Prove2me | Theorems.Thm_CollabProject_TimeDep_theorem_6_only_case
-- name    : CollabProject.TimeDep.theorem_6_only_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:43.263662+00:00
-- url     : https://prove2.me/theorems/94e38b00-2874-45ca-9f2c-7de31626625c
-- title:
--   Proof of Theorem 6 — only symmetric Case 2 can become shorter
-- statement:
--   Compare any symmetric-information subgame-perfect equilibrium with an asymmetric-information equilibrium for the same supplier and the true manufacturer type. The supplier's asymmetric choice maximizes expected payoff under its belief, and the true manufacturer best-responds after observing that choice. If the resulting project delay is strictly shorter under asymmetric information, then the symmetric game must be in Case 2 of Theorem 2:
--
--   $$
--   p^1_1<s_1\quad\text{and}\quad s_0<p^1_0.
--   $$
--
--   This is the necessity step stated at the start of the paper's proof of Theorem 6.
--
--   **Formalization Note** The statement makes positive savings and the no-tie regime explicit, with the belief probabilities computed from a finite-support distribution.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), Appendix p. 5 (PDF 37), proof of Theorem 6, first sentence

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- First sentence of the proof of Theorem 6: shortening is possible only
from Case 2 of Theorem 2. -/
theorem theorem_6_only_case {ι : Type} [Fintype ι]
    (S : SType) (M : MType) (B : Belief ι)
    (h : Standing S M) (hG : Generic S M)
    (hB : ∀ i, (B.θ i).Classed)
    (htie : S.s1 ≠ S.p11 * qLow B + S.p21 * qHigh B) :
    ∀ (a1 : Act) (σ0 : Act → Act) (b1 : Act)
      (σ : ι → Act → Act) (τ0 : Act → Act),
      IsSPNE S M a1 σ0 → IsAsymEq S B M b1 σ τ0 →
      delayCount b1 (τ0 b1) < delayCount a1 (σ0 a1) →
      S.p11 < S.s1 ∧ M.s0 < M.p10 := by sorry

end CollabProject.TimeDep
