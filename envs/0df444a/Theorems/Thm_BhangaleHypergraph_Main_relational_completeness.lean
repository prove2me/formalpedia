-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_relational_completeness
-- name    : BhangaleHypergraph.Main.relational_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:04.174092+00:00
-- url     : https://prove2.me/theorems/b4334daf-d96a-4e11-b9a0-e341fecfbb51
-- title:
--   Lemma 3.4 — Relational completeness
-- statement:
--   Let a finite outer constraint system have $C+1$ layers, $C\ge2$, positive vertex alphabets and total forward projections. Form the full closed domains and the generated quotient relation of §3.4. If one labeling satisfies every outer occurrence, then
--   $$\operatorname{Relational}(G,C)\text{ admits a satisfying 2-coloring}.$$
--   All local NAE triples are retained on the full closed domains, even when their quotient classes coincide.
--
--   This is the completeness property of the actual relational construction.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - generalization: an outer instance with a chain distribution → only its underlying layered constraints in the completeness statement; reason: the conclusion does not use the law and holds for every underlying layered system, including every source outer instance
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 3.4, p. 16 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Relational

namespace BhangaleHypergraph.Main

theorem relational_completeness (G : Layered) (C : ℕ) (hC : 2 ≤ C)
    (hlayers : G.layers = C + 1) (hsat : Satisfiable G) :
    RelColorable (Relational G C) 2 := by sorry

end BhangaleHypergraph.Main
