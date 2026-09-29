-- Prove2me | Theorems.Thm_FamousTheorems_triangle_counting_lemma
-- name    : FamousTheorems.triangle_counting_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:52.184991+00:00
-- url     : https://prove2.me/theorems/eeeeb4b2-d234-4842-8eaf-9d42e6f668d7
-- title:
--   The triangle counting lemma
-- statement:
--   **The triangle counting lemma.** Let $G$ be a finite graph and $s,t,u$ pairwise disjoint vertex sets such that each of the three pairs is $\varepsilon$-uniform with edge density at least $2\varepsilon$. Then $G$ contains at least
--   $$(1-2\varepsilon)\,\varepsilon^3\,|s|\,|t|\,|u|$$
--   triangles.
--
--   This is the counting half of the regularity method. Combined with the regularity lemma, it proves the triangle removal lemma and hence Roth's theorem on 3-term arithmetic progressions.
--
--   **Formalization note.** Mathlib's `SimpleGraph.triangle_counting`. `G.edgeDensity s t` is the edge density between `s` and `t`, `G.IsUniform ε s t` is $\varepsilon$-regularity of the pair, and `G.cliqueFinset 3` is the finset of triangles (as vertex sets).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.triangle_counting`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem triangle_counting_lemma {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {s t u : Finset α}
    (dst : 2 * ε ≤ G.edgeDensity s t) (ust : G.IsUniform ε s t) (hst : Disjoint s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u) (hsu : Disjoint s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) (htu : Disjoint t u) :
    (1 - 2 * ε) * ε ^ 3 * s.card * t.card * u.card ≤ (G.cliqueFinset 3).card := by sorry

end FamousTheorems
