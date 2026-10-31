-- Prove2me | Theorems.Thm_CollabProject_TimeDep_lemma_2_manufacturer
-- name    : CollabProject.TimeDep.lemma_2_manufacturer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:45.918386+00:00
-- url     : https://prove2.me/theorems/8075f1e4-0e18-46a9-82ea-75d278725cf0
-- title:
--   Lemma 2 — dominant actions for the manufacturer
-- statement:
--   In the two-firm serial project with time-dependent delay penalties, suppose Assumption 1(b) and Condition 2 hold. If the manufacturer's saving $s_0$ is below its first-period penalty share $p^1_0$, keeping its task duration gives it a strictly higher payoff than delaying, whether the supplier keeps or delays. If $s_0$ exceeds its second-period share $p^2_0$, delaying gives it a strictly higher payoff after either supplier action.
--
--   $$
--   s_0<p^1_0\ \Longrightarrow\ K\text{ strictly dominates }D,
--   \qquad p^2_0<s_0\ \Longrightarrow\ D\text{ strictly dominates }K.
--   $$
--
--   This identifies the two manufacturer classes whose responses are independent of the supplier's move.
--
--   **Formalization Note** Positive savings are explicit in the shared standing predicate, following the paper's cost interpretation.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 12 (PDF 12), Lemma 2, manufacturer clauses; proof, Appendix p. 1 (PDF 33)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- Lemma 2, manufacturer clause: the low-saving and high-saving types have
strictly dominant keep and delay actions, respectively. -/
theorem lemma_2_manufacturer (S : SType) (M : MType)
    (h : Standing S M) :
    (M.s0 < M.p10 → ∀ a1 : Act, u0 M a1 .delay < u0 M a1 .keep) ∧
    (M.p20 < M.s0 → ∀ a1 : Act, u0 M a1 .keep < u0 M a1 .delay) := by sorry

end CollabProject.TimeDep
