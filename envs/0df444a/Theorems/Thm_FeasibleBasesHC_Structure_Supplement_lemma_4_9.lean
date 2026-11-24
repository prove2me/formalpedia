-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_Supplement_lemma_4_9
-- name    : FeasibleBasesHC.Structure.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:31:25.247857+00:00
-- url     : https://prove2.me/theorems/69f06cea-1b37-4071-9166-05d6d1058976
-- title:
--   Lemma 4.9 — total transition count
-- statement:
--   Let $(s,\pi,L,U)$ be an encoded quadruple as specified in §4, p. 15, and let $\Gamma(G)$ denote the ultimate feasible bases (feasible for all discount factors sufficiently close to $1$ from below). Write $R=\{1\}$ and $W_{PQ}=\{i\in[n]\setminus\{s,s-1\}:i\in P,\ \pi(i)\in Q\}$. If $\pi(s)\in U$ and $s-1\in R\cup U$, then
--
--   $$|W_{UL}|+|W_{UR}|+|W_{RL}|=|W_{LU}|+1.$$
--
--   No feasibility or cardinality-balance assumption is required. The identity supplies the total count used to define the first-passage index $i^*$ in Remark 2.
--
--   **Formalization Note** The encoded basis, cyclic coefficients, and first-passage predicate are shared with every statement in this supplement. All flows and discounts are real, exactly as in the published base setting.
--
--   Differences from the source:
--   - encoding: Nodes are labelled 1 through n, with cyclic index arithmetic → Fin n with paper node i represented by i-1 and [NeZero n]; reason: The root is 0, the final node is -1, and no defined source instance is excluded
--   - reading: Feasible bases in the scope fixed on p. 6 → Membership in the published GamUlt for some loopless ambient graph containing the encoded arcs; reason: Feasible means eventually feasible as beta approaches 1 from below; nonbasic flows vanish, so all such ambient graphs give the same feasibility condition
--   - reading: The thin-arc bullet on p. 15 excludes s, while the displayed B and eta_i exclude s-1 → Use the displayed B: thin arcs (i,pi(i-1)) for i different from s; reason: This resolves the inconsistent descriptions using the displayed basis and the variable domain on pp. 15–16; the bullet otherwise includes the loop (s,s)
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 20, Lemma 4.9

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

namespace FeasibleBasesHC.Structure.Supplement

theorem lemma_4_9 {n : ℕ} [NeZero n] (q : Quadruple n)
    (hpi : q.pi q.s ∈ q.U) (hprev : q.s - 1 ∈ R n ∪ q.U) :
    (W q q.U q.L).card + (W q q.U (R n)).card + (W q (R n) q.L).card =
      (W q q.L q.U).card + 1 := by sorry

end FeasibleBasesHC.Structure.Supplement
