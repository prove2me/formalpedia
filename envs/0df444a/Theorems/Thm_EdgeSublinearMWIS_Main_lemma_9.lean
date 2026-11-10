-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_9
-- name    : EdgeSublinearMWIS.Main.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:09.156198+00:00
-- url     : https://prove2.me/theorems/da63e145-88fb-40e4-9b29-751367d11f95
-- title:
--   Lemma 9 — transfer tree-decompositions through almost-embeddings
-- statement:
--   Let $H$ have maximum degree at most $d$ and no isolated vertices, and let an almost-embedding of $H$ in $G$ be given. For every tree-decomposition of $G$ whose bags have size at most $w$, there are bags on the same decomposition tree forming a tree-decomposition of $H$ with
--   $$|B'_t|\le2dw\quad\text{for every tree node }t.$$
--   The embedding need not be induced or injective, and singleton edge paths are permitted. This transfer connects the sampled almost-embedded graph to the host's treewidth.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - generalization: finite decomposition trees under the section convention → arbitrary decomposition-tree carriers with the same finite bags; reason: the source finite trees are included; the path running-intersection argument also applies to infinite trees
--   - encoding: a decomposition is obtained from each input decomposition → the new bags use the same tree; reason: this is the transfer constructed in the source proof
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 9, p.9 (PDF p.9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

namespace EdgeSublinearMWIS.Main

/-- Lemma 9: no inducedness or injectivity is imposed. The same tree carries the
transferred bags, also when the original decomposition tree is infinite. -/
theorem lemma_9 {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (d w : ℕ) (hdegree : ∀ v, degree H v ≤ d) (hisolated : ∀ v, ∃ u, H.Adj v u)
    (embedding : AlmostEmbedding H G) (T : Type) (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (decomposition : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (size : ∀ t, (bags t).card ≤ w) :
    ∃ newBags : T → Finset (Fin h),
      RobertsonSeymour1986.GM5.IsTreeDecomposition H tree newBags ∧
        ∀ t, (newBags t).card ≤ 2 * d * w := by sorry

end EdgeSublinearMWIS.Main
