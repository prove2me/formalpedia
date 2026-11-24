-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_Supplement_theorem_4_2
-- name    : FeasibleBasesHC.Structure.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:32:09.407656+00:00
-- url     : https://prove2.me/theorems/a483ed39-b188-4209-b151-0d9ac29639b2
-- title:
--   Theorem 4.2 — odd-node feasibility criterion
-- statement:
--   Let $(s,\pi,L,U)$ be an encoded quadruple as specified in §4, p. 15, and let $\Gamma(G)$ denote the ultimate feasible bases (feasible for all discount factors sufficiently close to $1$ from below). Let $n=2k+1$. Its basis is ultimate feasible if and only if
--
--   $$|U|=k-1,\quad |L|=k,\quad \pi(s)\in U,\quad s-1\in R=\{1\},\quad i^*=n.$$
--
--   The index $i^*$ is the first index in cyclic order $s+1,\ldots,s-2$ where $N_{UL}+N_{UR}+N_{RL}-N_{LU}$ equals $1$. Its existence and uniqueness under the middle conditions are the content of Remark 2; Lean expresses the last condition by applying its defining predicate to the final node. This companion theorem specializes the general criterion to an odd number of nodes. No $n\ge5$ hypothesis is added: at $n=1$ and $n=3$ no encoded quadruple exists.
--
--   **Formalization Note** The encoded basis, cyclic coefficients, and first-passage predicate are shared with every statement in this supplement. All flows and discounts are real, exactly as in the published base setting.
--
--   Differences from the source:
--   - encoding: Nodes are labelled 1 through n, with cyclic index arithmetic → Fin n with paper node i represented by i-1 and [NeZero n]; reason: The root is 0, the final node is -1, and no defined source instance is excluded
--   - reading: Feasible bases in the scope fixed on p. 6 → Membership in the published GamUlt for some loopless ambient graph containing the encoded arcs; reason: Feasible means eventually feasible as beta approaches 1 from below; nonbasic flows vanish, so all such ambient graphs give the same feasibility condition
--   - reading: The thin-arc bullet on p. 15 excludes s, while the displayed B and eta_i exclude s-1 → Use the displayed B: thin arcs (i,pi(i-1)) for i different from s; reason: This resolves the inconsistent descriptions using the displayed basis and the variable domain on pp. 15–16; the bullet otherwise includes the loop (s,s)
--   - encoding: The well-defined first-passage index i* equals node n → IsIStar q (-1); reason: Remark 2 gives uniqueness under conditions (ii) and (iii); the last node is -1 in zero-based cyclic labels, so this retains existence and the specified equality
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 21, Theorem 4.2 (statement continues on p. 22)

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

namespace FeasibleBasesHC.Structure.Supplement

theorem theorem_4_2 {n : ℕ} [NeZero n] (k : ℕ)
    (hn : n = 2 * k + 1) (q : Quadruple n) :
    q.Feasible ↔
      (q.U.card = k - 1 ∧ q.L.card = k) ∧
      q.pi q.s ∈ q.U ∧ q.s - 1 ∈ R n ∧ IsIStar q (-1) := by sorry

end FeasibleBasesHC.Structure.Supplement
