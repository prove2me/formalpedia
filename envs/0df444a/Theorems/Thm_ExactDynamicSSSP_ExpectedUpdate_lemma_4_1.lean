-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_1
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:26:27.566163+00:00
-- url     : https://prove2.me/theorems/349e501c-1e8c-4b96-90d8-cd6a3a243ee0
-- title:
--   Lemma 4.1 — vertices whose distance decreases are reachable from the updated head
-- statement:
--   Let $G$ be a weighted digraph and let $G'$ arise from $G$ by a distance-decreasing update of the arc $u\to v$ (insertion of an absent arc, or a strict decrease of its weight). Let
--   $$A=\{x : d^t_x<d^{t-1}_x\}$$
--   be the set of vertices whose distance from the source $s$ strictly decreases. Then every vertex of $A$ is reachable from $v$ in $G'$. Equivalently, every vertex $p$ not reachable from $v$ in $G'$ keeps its distance: $d^t_p=d^{t-1}_p$.
--
--   This locality statement is the reason Algorithm 1 can start its propagation at $v$.
--
--   Differences from the source:
--   - encoding: distances are minima over paths → dist is the infimum in [0,∞] of walk weights (⊤ when no walk exists); reason: with nonnegative weights the infimum over walks equals the minimum over simple paths
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.1, PDF p.5 = printed p.5

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.1 (PDF p. 5). In a distance-decreasing update of the arc `u → v`, every vertex whose
distance strictly decreases is reachable from `v` in the updated graph; equivalently, a vertex
not reachable from `v` keeps its distance. -/
theorem lemma_4_1 {n : ℕ} (G G' : WDigraph n) (s u v : Fin n)
    (hupd : IsDecreasingUpdate G G' u v) :
    (∀ x, G'.dist s x < G.dist s x → G'.Reach v x) ∧
    (∀ p, ¬ G'.Reach v p → G'.dist s p = G.dist s p) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
