-- Prove2me | Theorems.Thm_ConstRegretMatch_Acyclic_lemma_C_1_leaves
-- name    : ConstRegretMatch.Acyclic.lemma_C_1_leaves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:35.920725+00:00
-- url     : https://prove2.me/theorems/917f8683-cbbe-464e-8808-c517a4257ef6
-- title:
--   Lemma C.1, p. 44 (first sentence) — a connected acyclic matching network graph has at least n − d + 1 leaves
-- statement:
--   Let a matching network have $n$ agent types and $d$ matches, every match using at least two types and every type taking part in at least one match. Suppose its matching network graph $\mathcal G$ (the bipartite type–match incidence graph) is connected and acyclic. Then the number $L$ of leaves of $\mathcal G$ (vertices of degree one) satisfies
--   $$L \ \ge\ n - d + 1.$$
--
--   In Appendix C this count is used to show that some over-demanded queue is a leaf, which is the starting point of the explicit construction of the inverse of the optimal basis.
--
--   **Formalization Note** The inequality is written $n + 1 \le L + d$ to avoid natural-number subtraction. Leaves are counted among all vertices of $\mathcal G$; since $|\mathcal A(m)| \ge 2$, match vertices never are leaves, so $L$ is the number of types that take part in exactly one match.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 44, Lemma C.1 (first sentence); proof pp. 46–47

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network

namespace ConstRegretMatch.Acyclic

/-- Lemma C.1, p. 44 (first sentence; proof pp. 46–47): if the matching network graph `𝒢` of a
matching network with `n` agent types and `d` matches is connected and acyclic, then the number of
leaves (vertices of degree one) of `𝒢` is at least `n - d + 1`, written without subtraction. -/
theorem lemma_C_1_leaves {n d : ℕ} (N : MatchingNetwork n d)
    (hconn : (networkGraph N).Connected) (hacyc : (networkGraph N).IsAcyclic) :
    n + 1 ≤ (leaves (networkGraph N)).card + d := by sorry

end ConstRegretMatch.Acyclic
