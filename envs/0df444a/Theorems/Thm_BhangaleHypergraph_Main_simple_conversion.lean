-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_simple_conversion
-- name    : BhangaleHypergraph.Main.simple_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:05.020203+00:00
-- url     : https://prove2.me/theorems/ad87d469-b58f-4c45-9bef-a78425a49d71
-- title:
--   Lemma 3.6 — Conversion to a simple hypergraph
-- statement:
--   Let a finite relational NAE instance $I$ have arbitrary ordered triples, allowing every repetition pattern. Form $H$ by replacing each vertex with $2C+1$ copies and inserting every three-distinct-vertex set drawn from a relational triple, with duplicate edges removed. For $C\ge2$,
--   $$I\text{ is 2-colorable}\Longrightarrow H\text{ is 2-colorable},$$
--   $$H\text{ is C-colorable}\Longrightarrow I\text{ has a satisfying C-coloring}.$$
--   Both implications hold for every bijective numbering of the cluster vertices.
--
--   This is the complete simple-hypergraph conversion guarantee.
--
--   Differences from the source:
--   - generalization: the relational quotient instance constructed in §3.4 → any finite ternary relational instance; reason: the conversion and both implications apply to every such instance, in particular the source quotient
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: cluster vertices (v,i) → an arbitrary bijection from Fin n onto all cluster vertices; reason: a bijective renaming changes no edge or coloring instance; it does not assume correctness
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 3.6, p. 18 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Relational

namespace BhangaleHypergraph.Main

theorem simple_conversion {V : Type} [Fintype V] (I : RelInstance V) (C n : ℕ)
    (hC : 2 ≤ C) (numbering : Fin n ≃ V × Fin (2 * C + 1)) :
    (RelColorable I 2 → (Cluster I C n numbering).Colorable 2) ∧
    ((Cluster I C n numbering).Colorable C → RelColorable I C) := by sorry

end BhangaleHypergraph.Main
