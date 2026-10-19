-- Prove2me | Theorems.Thm_CollabProject_TimeDep_theorem_2
-- name    : CollabProject.TimeDep.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:48.100978+00:00
-- url     : https://prove2.me/theorems/4c34798b-b0f2-4e3e-b87c-a6595e7f8743
-- title:
--   Theorem 2 — five equilibrium cases under symmetric information
-- statement:
--   Under Assumption 1(b) and Condition 2, the two-stage game has a subgame-perfect equilibrium. With payoff ties excluded, every such equilibrium has one of the following five outcomes, where $K$ means keep and $D$ means delay. The ordered pair lists the supplier's action and the manufacturer's response.
--
--   | Case | Conditions | Outcome |
--   |---|---|---|
--   | 1 | $s_1<p^1_1$, $s_0<p^1_0$ | $(K,K)$ |
--   | 2 | $p^1_1<s_1$, $s_0<p^1_0$ | $(D,K)$ |
--   | 3 | $p^1_0<s_0<p^2_0$, for either supplier saving class | $(D,K)$ |
--   | 4 | $s_1<p^2_1$, $p^2_0<s_0$ | $(K,D)$ |
--   | 5 | $p^2_1<s_1$, $p^2_0<s_0$ | $(D,D)$ |
--
--   This table supplies the symmetric-information duration against which Theorem 6 compares asymmetric information.
--
--   **Formalization Note** The statement requires positive savings and excludes the four payoff ties at the thresholds in the table. It asserts equilibrium existence and classifies all equilibrium outcomes; the outcomes are derived from payoff maximization rather than defined by the table.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 12 (PDF 12), Theorem 2 and case table; proof, Appendix p. 2 (PDF 34)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- Theorem 2: existence and the five rows of the subgame-perfect equilibrium
table, with the third row independent of the supplier's saving class. -/
theorem theorem_2 (S : SType) (M : MType)
    (h : Standing S M) (hG : Generic S M) :
    (∃ a1 : Act, ∃ σ0 : Act → Act, IsSPNE S M a1 σ0) ∧
    ∀ (a1 : Act) (σ0 : Act → Act), IsSPNE S M a1 σ0 →
      (S.s1 < S.p11 ∧ M.s0 < M.p10 ∧ a1 = .keep ∧ σ0 a1 = .keep) ∨
      (S.p11 < S.s1 ∧ M.s0 < M.p10 ∧ a1 = .delay ∧ σ0 a1 = .keep) ∨
      (M.p10 < M.s0 ∧ M.s0 < M.p20 ∧ a1 = .delay ∧ σ0 a1 = .keep) ∨
      (S.s1 < S.p21 ∧ M.p20 < M.s0 ∧ a1 = .keep ∧ σ0 a1 = .delay) ∨
      (S.p21 < S.s1 ∧ M.p20 < M.s0 ∧ a1 = .delay ∧ σ0 a1 = .delay) := by sorry

end CollabProject.TimeDep
