-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_theorem_5
-- name    : EdgeSublinearMWIS.Main.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:07.638206+00:00
-- url     : https://prove2.me/theorems/8aefbb9a-6bc5-48a5-9c9a-99ca9e4bbb66
-- title:
--   Theorem 5 — treewidth and separation number
-- statement:
--   For every finite graph $G$ with at least one edge, treewidth and the separation number are comparable with two universal positive constants $c,K$:
--   $$c\,\operatorname{sn}(G)\le\operatorname{tw}(G)\le K\,\operatorname{sn}(G).$$
--   Here $\operatorname{sn}(G)$ bounds balanced separator cardinalities in every induced subgraph. The constants precede the graph. This comparison supplies the treewidth interpretation of the separator hypothesis.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: Theta notation → both inequalities with universal positive constants; reason: neither comparison nor uniformity is dropped
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 5, p.5 (PDF p.5), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs

namespace EdgeSublinearMWIS.Main

/-- Both comparisons are uniform over every graph with an edge. -/
theorem theorem_5 :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      1 ≤ edgeCount G →
        c * separationNumber G ≤ (PlantedSubgraphLD.tw G : ℝ) ∧
          (PlantedSubgraphLD.tw G : ℝ) ≤ K * separationNumber G := by sorry

end EdgeSublinearMWIS.Main
