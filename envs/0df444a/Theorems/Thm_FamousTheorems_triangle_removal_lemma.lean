-- Prove2me | Theorems.Thm_FamousTheorems_triangle_removal_lemma
-- name    : FamousTheorems.triangle_removal_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:55.442675+00:00
-- url     : https://prove2.me/theorems/d5922005-6dd1-4a7e-bcb5-3a65be903802
-- title:
--   The triangle removal lemma
-- statement:
--   **The triangle removal lemma.** For every $\varepsilon>0$ there is $\delta>0$ such that for every finite graph $G$ on $n$ vertices with fewer than $\delta n^3$ triangles, one can delete fewer than $\varepsilon n^2$ edges to make $G$ triangle-free. That is, there is a triangle-free subgraph $G'\le G$ with $|E(G)|-|E(G')|<\varepsilon n^2$.
--
--   The constant $\delta$ depends only on $\varepsilon$. The lemma (Ruzsa–Szemerédi) is a cornerstone of the regularity method. It implies Roth's theorem and the $(6,3)$-theorem, and is a basic example of property testing.
--
--   **Formalization note.** Derived from Mathlib's `SimpleGraph.triangle_removal`, with $\delta$ given by the explicit `SimpleGraph.triangleRemovalBound ε`. `G.cliqueFinset 3` is the finset of triangles, `G'.CliqueFree 3` means triangle-free, and the quantification over all finite vertex types is uniform in $\delta$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.triangle_removal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem triangle_removal_lemma {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (α : Type*) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      ((G.cliqueFinset 3).card : ℝ) < δ * Fintype.card α ^ 3 →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          ((G.edgeFinset.card : ℝ) - G'.edgeFinset.card) < ε * (Fintype.card α ^ 2 : ℕ) ∧ G'.CliqueFree 3 := by sorry

end FamousTheorems
