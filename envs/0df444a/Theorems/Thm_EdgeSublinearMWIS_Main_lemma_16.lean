-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_16
-- name    : EdgeSublinearMWIS.Main.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:40:57.333215+00:00
-- url     : https://prove2.me/theorems/bf5f156e-d0ae-41b6-abd5-f00506038a59
-- title:
--   Lemma 16 — independent blow-ups preserve the separator property
-- statement:
--   If $\mathcal C$ is hereditary and satisfies the uniform treewidth bound (2) with integer $a\ge2$, its independent blow-up class $\mathcal C^{\mathrm{bl}}$ is hereditary. There is $B>0$, fixed before every blow-up graph, such that each $m$-edge member $H$ satisfies
--   $$\operatorname{tw}(H)\le Bm^{1-1/(2a)}.$$
--   Furthermore, $\mathcal C^{\mathrm{bl}}$ has strongly edge-sublinear separators. Fibers are nonempty independent sets and edges between fibers follow the original adjacency exactly. All three conclusions are included. Edgeless blow-ups are covered with treewidth zero. This is the closure property needed to pass from unweighted to weighted independent set.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: independent blow-ups with nonempty fibers → surjective maps of finite label sets preserving adjacency exactly; reason: surjectivity is precisely nonempty fibers; no bound on fiber sizes is imposed
--   - encoding: O_C(m^(1-1/(2a))) → a uniform positive multiplier with the same real exponent, including m=0; reason: the proof explicitly treats edgeless graphs
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 16, p.19 (PDF p.19), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs

namespace EdgeSublinearMWIS.Main

/-- All orders and edge counts, including edgeless blow-ups. -/
theorem lemma_16 (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    Hereditary (BlowupClass C) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)), BlowupClass C m H →
        (PlantedSubgraphLD.tw H : ℝ) ≤
          B * (edgeCount H : ℝ) ^ (1 - 1 / (2 * (a : ℝ)))) ∧
      StronglyEdgeSublinear (BlowupClass C) := by sorry

end EdgeSublinearMWIS.Main
