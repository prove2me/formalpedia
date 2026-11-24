-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_Supplement_theorem_4_1
-- name    : FeasibleBasesHC.Structure.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:29:40.011805+00:00
-- url     : https://prove2.me/theorems/ee4247f2-3319-4f72-b311-0589556749bb
-- title:
--   Theorem 4.1 — exact first-order feasibility criterion
-- statement:
--   Let $(s,\pi,L,U)$ be an encoded quadruple as specified in §4, p. 15, and let $\Gamma(G)$ denote the ultimate feasible bases (feasible for all discount factors sufficiently close to $1$ from below). For $n\ge5$, its encoded basis is ultimate feasible if and only if all three conditions hold:
--
--   $$|U|=\left\lfloor\frac{n-2}{2}\right\rfloor,\quad |L|=\left\lceil\frac{n-2}{2}\right\rceil,\qquad \pi(s)\in U,$$
--   $$\alpha_{s1}+\sum_{j\in I(i)}\alpha_{j1}\ge0\qquad(i\in[n]\setminus\{s,s-1\}).$$
--
--   Here the first-order coefficients and the cyclic initial segments are the exact objects defined on pp. 18–19. Both necessity and sufficiency are posed. This companion theorem gives the general finite criterion from which the odd and even criteria are derived.
--
--   **Formalization Note** The encoded basis, cyclic coefficients, and first-passage predicate are shared with every statement in this supplement. All flows and discounts are real, exactly as in the published base setting.
--
--   Differences from the source:
--   - encoding: Nodes are labelled 1 through n, with cyclic index arithmetic → Fin n with paper node i represented by i-1 and [NeZero n]; reason: The root is 0, the final node is -1, and no defined source instance is excluded
--   - reading: Feasible bases in the scope fixed on p. 6 → Membership in the published GamUlt for some loopless ambient graph containing the encoded arcs; reason: Feasible means eventually feasible as beta approaches 1 from below; nonbasic flows vanish, so all such ambient graphs give the same feasibility condition
--   - reading: The thin-arc bullet on p. 15 excludes s, while the displayed B and eta_i exclude s-1 → Use the displayed B: thin arcs (i,pi(i-1)) for i different from s; reason: This resolves the inconsistent descriptions using the displayed basis and the variable domain on pp. 15–16; the bullet otherwise includes the loop (s,s)
--   - encoding: Floor and ceiling cardinalities and integer partial sums → Natural quotients (n-2)/2 and (n-1)/2, with alphaS and alpha1 in the integers; reason: For n at least 5 these are the same cardinalities and exact coefficients
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 20, Theorem 4.1

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

namespace FeasibleBasesHC.Structure.Supplement

theorem theorem_4_1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (q : Quadruple n) :
    q.Feasible ↔
      (q.U.card = (n - 2) / 2 ∧ q.L.card = (n - 1) / 2) ∧
      q.pi q.s ∈ q.U ∧
      ∀ i ∈ active q, 0 ≤ alphaS n + ∑ j ∈ I q i, alpha1 q j := by sorry

end FeasibleBasesHC.Structure.Supplement
