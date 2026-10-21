-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_4
-- name    : FeasibleBasesHC.Structure.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:09.645982+00:00
-- url     : https://prove2.me/theorems/61cf8ca5-f919-409b-b5ee-b53f582e17f7
-- title:
--   Theorem 3.4(i)–(ii), p. 14 — the connected basis and unique thick matching
-- statement:
--   Let $(B,L,U)\in\Gamma(G)$ be an ultimate feasible basis, $B'$ its split-graph basic arc set, $Y'$ its basic slack arcs, and $A'_1$ its thick arcs. Then
--
--   $$B'\text{ is a good augmented tree spanning }G',\qquad A'_1\text{ is the unique perfect matching contained in }B'\setminus Y'.$$
--
--   In particular, every split vertex is incident with exactly one thick arc. The matching is unique among those using the basic original arcs; this is the reading established in the paper's proof. The printed claim of uniqueness in all of $G'$ is false when $G$ has another cycle cover. Clause (iii) of the printed theorem is false and is not posed.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. Goodness holds at every $0<\beta<1$. Degenerate bases remain in scope, and matching uniqueness is quantified over all subsets of $B'\setminus Y'$.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 14, Theorem 3.4 (i)–(ii), with uniqueness read from the proof

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Theorem 3.4(i)--(ii), with uniqueness of the matching inside B′ minus Y′,
    as established by the proof on p. 14. -/
theorem theorem_3_4 {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    ∀ beta : ℝ, 0 < beta → beta < 1 →
      (Gp G beta).IsGoodAugTree (Bp b) ∧
      (Gp G beta).IsPerfectMatching ((thickArcs G b).image Sum.inl) ∧
      (∀ M : Finset (GpArc n), M ⊆ b.A.image Sum.inl →
        (Gp G beta).IsPerfectMatching M → M = (thickArcs G b).image Sum.inl) := by sorry

end FeasibleBasesHC.Structure
