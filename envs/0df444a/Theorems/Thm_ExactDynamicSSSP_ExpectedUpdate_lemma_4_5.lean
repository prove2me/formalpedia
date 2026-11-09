-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_5
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:26:38.399824+00:00
-- url     : https://prove2.me/theorems/581a8d9b-c36d-449c-a744-9b6c270eee47
-- title:
--   Lemma 4.5 — arcs entering the affected subtree give valid boundary candidates
-- statement:
--   Let $\mathrm{par}$ be a shortest-path tree of $G$ rooted at $s$, let $u\to v$ be a tree arc, and let $G'$ arise by deleting it or strictly increasing its weight. For every arc $x\to y$ of $G'$ with weight $w$, $y\in V(SPT_v)$ and $x\notin V(SPT_v)$:
--
--   1. the tail's old distance is still exact, $d_{G'}(s,x)=d_G(s,x)$;
--   2. the boundary candidate is a feasible upper bound, $d_{G'}(s,y)\le d_G(s,x)+w$.
--
--   So replacement paths entering $V(SPT_v)$ from outside provide valid initialization values for the local recomputation, even though the old distances inside the subtree may no longer be optimal.
--
--   Differences from the source:
--   - encoding: distances are minima over paths → dist is the infimum in [0,∞] of walk weights (⊤ when no walk exists); reason: with nonnegative weights the infimum over walks equals the minimum over simple paths
--   - reading: 'replacement paths entering V(SPT_v) from outside the subtree provide valid boundary initialization candidates' → for every entering arc (x,y) of the updated graph: d'(x) = d(x) and d'(y) ≤ d(x) + w(x,y); reason: validity of a candidate means its prefix distance is exact and it is the weight of a feasible walk, as in the lemma's proof
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.5, PDF p.6 = printed p.6

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.5 (PDF p. 6). For an increasing update of the tree arc `u → v` of a shortest-path
tree `par`, every arc `x → y` of the updated graph entering `V(SPT_v)` from outside supplies a
valid boundary initialization candidate: the prefix distance of its tail is already exact,
`d^t_x = d^{t-1}_x`, and `d^{t-1}_x + w(x,y)` is the weight of a walk to `y` in the updated
graph, hence an upper bound on `d^t_y`. -/
theorem lemma_4_5 {n : ℕ} (G G' : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n))
    (hT : IsSPT G s par) (u v : Fin n) (htree : par v = some u)
    (hupd : IsIncreasingUpdate G G' u v) :
    ∀ x y (w : ℝ≥0), y ∈ subtree s par v → x ∉ subtree s par v → G'.wt x y = some w →
      G'.dist s x = G.dist s x ∧ G'.dist s y ≤ G.dist s x + (w : ℝ≥0∞) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
