-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_composition
-- name    : BhangaleHypergraph.Main.composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:13.687204+00:00
-- url     : https://prove2.me/theorems/43684b19-7f77-4aa3-b978-ad25a275ed64
-- title:
--   Proposition 3.7 — Composition with exact color gap
-- statement:
--   For $C\ge2$, let $G$ be an outer instance with $C+1$ layers, positive vertex-dependent alphabets, total forward occurrences and an actual chain law. Apply the full closed-domain, generated-quotient and $2C+1$-cluster construction. Its simple 3-uniform output $H$ satisfies both clauses:
--
--   1. If $G$ has a labeling satisfying every occurrence, then $H$ is 2-colorable.
--   2. If $G$ has pairwise soundness $\varepsilon$ with
--   $$\varepsilon<\frac1{\binom{C+1}{2}(2C)^{2C}},$$
--   then $H$ has no proper $C$-coloring, equivalently $\chi(H)>C$.
--
--   The construction is the defined one and every bijective vertex numbering is allowed. This proposition does not replace the growing-color goal.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: χ(H)>C → absence of a proper C-coloring of the defined output; reason: these are equivalent for a finite simple hypergraph
--   - encoding: unnumbered quotient clusters → all bijective numberings of precisely those clusters; reason: the statement is invariant under renaming and does not range over unrelated hypergraphs
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Proposition 3.7, p. 18 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Relational

namespace BhangaleHypergraph.Main

theorem composition (G : Outer) (C n : ℕ) (hC : 2 ≤ C) (hlayers : G.layers = C + 1)
    (numbering : Fin n ≃ RelVertex G.toLayered C × Fin (2 * C + 1)) :
    (Satisfiable G.toLayered → (Composed G.toLayered C n numbering).Colorable 2) ∧
    (∀ ε : ℝ, PairwiseSound G ε →
      ε < 1 / ((Nat.choose (C + 1) 2 : ℝ) * ((2 * C : ℕ) : ℝ) ^ (2 * C)) →
        ¬ (Composed G.toLayered C n numbering).Colorable C) := by sorry

end BhangaleHypergraph.Main
