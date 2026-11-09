-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_4
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:26:31.224608+00:00
-- url     : https://prove2.me/theorems/978fa41c-d7fd-4d07-b95e-f062ab12b8ba
-- title:
--   Lemma 4.4 — distance-increasing updates only affect the subtree below the updated tree arc
-- statement:
--   Let $\mathrm{par}$ be a shortest-path tree of $G$ rooted at $s$, let $u\to v$ be one of its arcs ($\mathrm{par}(v)=u$), and let $G'$ arise from $G$ by deleting $u\to v$ or strictly increasing its weight. Then every vertex whose distance changes lies in $V(SPT_v)$:
--   $$d_{G'}(s,p)\ne d_G(s,p)\ \Longrightarrow\ p\in V(SPT_v),$$
--   and every vertex $p\notin V(SPT_v)$ keeps its distance.
--
--   Differences from the source:
--   - encoding: distances are minima over paths → dist is the infimum in [0,∞] of walk weights (⊤ when no walk exists); reason: with nonnegative weights the infimum over walks equals the minimum over simple paths
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.4, PDF p.6 = printed p.6

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.4 (PDF p. 6). If `u → v` is an arc of a shortest-path tree `par` of `G` (so
`par v = u`) and the update deletes it or strictly increases its weight, then every vertex whose
distance changes lies in `V(SPT_v)`; every vertex outside `V(SPT_v)` keeps its distance. -/
theorem lemma_4_4 {n : ℕ} (G G' : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n))
    (hT : IsSPT G s par) (u v : Fin n) (htree : par v = some u)
    (hupd : IsIncreasingUpdate G G' u v) :
    (∀ p, G'.dist s p ≠ G.dist s p → p ∈ subtree s par v) ∧
    (∀ p, p ∉ subtree s par v → G'.dist s p = G.dist s p) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
