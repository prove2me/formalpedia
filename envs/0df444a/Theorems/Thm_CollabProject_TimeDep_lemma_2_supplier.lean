-- Prove2me | Theorems.Thm_CollabProject_TimeDep_lemma_2_supplier
-- name    : CollabProject.TimeDep.lemma_2_supplier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:45.435429+00:00
-- url     : https://prove2.me/theorems/a9e6bdb1-cc58-4702-b6fa-8210cc48b8da
-- title:
--   Lemma 2 — supplier delays against every manufacturer best response
-- statement:
--   Suppose the supplier's first- and second-period penalty shares satisfy $p^1_1<p^2_1<s_1$. For every manufacturer cost type satisfying the model's standing assumptions, and for every strategy that best-responds after each supplier move, the supplier's payoff from delaying is strictly greater than its payoff from keeping:
--
--   $$
--   u_1(D,\sigma_0(D))>u_1(K,\sigma_0(K)).
--   $$
--
--   This is the supplier clause of Lemma 2 and identifies a regime where the supplier's equilibrium action does not depend on which manufacturer type it faces.
--
--   **Formalization Note** The paper's proof compares the supplier's two choices against each manufacturer's best response. The statement uses that reading of “dominant”; it does not claim dominance against arbitrary, nonoptimal manufacturer strategies. Positive savings are explicit in the standing predicate.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 12 (PDF 12), Lemma 2, supplier clause; proof, Appendix pp. 1–2 (PDF 33–34)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

namespace CollabProject.TimeDep

/-- Lemma 2, supplier clause, with dominance interpreted against each possible
manufacturer type's best-response strategy as in the paper's proof. -/
theorem lemma_2_supplier (S : SType)
    (hS : S.p11 < S.p21 ∧ S.p21 < S.s1) :
    ∀ (M : MType), Standing S M →
      ∀ (σ0 : Act → Act), (∀ a, IsBR0 M a (σ0 a)) →
        u1 S .keep (σ0 .keep) < u1 S .delay (σ0 .delay) := by sorry

end CollabProject.TimeDep
