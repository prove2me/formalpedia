-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_10
-- name    : EdgeSublinearMWIS.Main.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:05.917201+00:00
-- url     : https://prove2.me/theorems/a4195cfe-addb-4e81-96bc-eefd817f91f9
-- title:
--   Lemma 10 — subcubic graphs of linear treewidth
-- statement:
--   There are universal $c>0$ and integer $t_0$ such that every integer $t\ge t_0$ admits a graph $H$ with exactly $t$ vertices, maximum degree at most three, and
--   $$\operatorname{tw}(H)\ge ct.$$
--   The constants are chosen before $t$. No construction-time assertion is added and no subsequence of orders is substituted. This supplies the graph used in the path-distribution obstruction.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: sufficiently large t and Omega(t) → a universal threshold and a universal positive lower comparison constant; reason: no numerical expander constant is supplied by the source
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 10, p.9 (PDF p.9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs

namespace EdgeSublinearMWIS.Main

/-- Every sufficiently large order, not merely a subsequence. -/
theorem lemma_10 :
    ∃ (c : ℝ) (t₀ : ℕ), 0 < c ∧ ∀ t ≥ t₀,
      ∃ H : SimpleGraph (Fin t), (∀ v, degree H v ≤ 3) ∧
        c * t ≤ (PlantedSubgraphLD.tw H : ℝ) := by sorry

end EdgeSublinearMWIS.Main
