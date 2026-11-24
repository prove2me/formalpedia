-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_Supplement_lemma_4_3
-- name    : FeasibleBasesHC.Structure.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:28:45.234725+00:00
-- url     : https://prove2.me/theorems/fa2b19cc-293b-4cae-bade-bde8964a581e
-- title:
--   Lemma 4.3 — slack cardinalities
-- statement:
--   Let $(s,\pi,L,U)$ be an encoded quadruple as specified in §4, p. 15, and let $\Gamma(G)$ denote the ultimate feasible bases (feasible for all discount factors sufficiently close to $1$ from below). If it encodes an ultimate feasible basis, then
--
--   $$|U|=\left\lfloor\frac{n-2}{2}\right\rfloor,\qquad |L|=\left\lceil\frac{n-2}{2}\right\rceil.$$
--
--   This supplies the cardinality condition in Theorem 4.1 and in both parity characterizations.
--
--   **Formalization Note** The encoded basis, cyclic coefficients, and first-passage predicate are shared with every statement in this supplement. All flows and discounts are real, exactly as in the published base setting.
--
--   Differences from the source:
--   - encoding: Nodes are labelled 1 through n, with cyclic index arithmetic → Fin n with paper node i represented by i-1 and [NeZero n]; reason: The root is 0, the final node is -1, and no defined source instance is excluded
--   - reading: Feasible bases in the scope fixed on p. 6 → Membership in the published GamUlt for some loopless ambient graph containing the encoded arcs; reason: Feasible means eventually feasible as beta approaches 1 from below; nonbasic flows vanish, so all such ambient graphs give the same feasibility condition
--   - reading: The thin-arc bullet on p. 15 excludes s, while the displayed B and eta_i exclude s-1 → Use the displayed B: thin arcs (i,pi(i-1)) for i different from s; reason: This resolves the inconsistent descriptions using the displayed basis and the variable domain on pp. 15–16; the bullet otherwise includes the loop (s,s)
--   - encoding: Floor and ceiling of (n-2)/2 → Natural quotients (n-2)/2 and (n-1)/2; reason: s differs from the root, so n is at least 2 and these are exactly the stated floor and ceiling
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 17, Lemma 4.3

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Quadruple

namespace FeasibleBasesHC.Structure.Supplement

theorem lemma_4_3 {n : ℕ} [NeZero n] (q : Quadruple n)
    (hfeas : q.Feasible) :
    q.U.card = (n - 2) / 2 ∧ q.L.card = (n - 1) / 2 := by sorry

end FeasibleBasesHC.Structure.Supplement
