-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_2
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:27:07.257067+00:00
-- url     : https://prove2.me/theorems/2c0a5795-d76c-4d0f-b688-d784fb1de9a0
-- title:
--   Lemma 4.2 — the three cases of a distance-decreasing update
-- statement:
--   Let $G'$ arise from $G$ by a distance-decreasing update of the arc $u\to v$, and for a vertex $x$ let $d^t(e'_x)$ be the least weight of a simple path from $s$ to $x$ in $G'$ that traverses $u\to v$ ($+\infty$ if there is none). Then:
--
--   1. if $x$ is not reachable from $v$ in $G'$, its distance is unchanged, $d^t_x=d^{t-1}_x$;
--   2. if $x$ is reachable from $v$ and $d^t(e'_x)\ge d^{t-1}_x$, then $x$ has no strict distance decrease, $\neg(d^t_x<d^{t-1}_x)$;
--   3. if $x$ is reachable from $v$ and $d^t(e'_x)<d^{t-1}_x$, then $x$ belongs to the affected region, $d^t_x<d^{t-1}_x$.
--
--   The cases describe where the propagation of Algorithm 1 must continue and where it stops.
--
--   Differences from the source:
--   - encoding: distances are minima over paths → dist is the infimum in [0,∞] of walk weights (⊤ when no walk exists); reason: with nonnegative weights the infimum over walks equals the minimum over simple paths
--   - reading: 'does not need to be updated' (1), 'does not need further propagation' (2), 'belongs to the affected region and needs further propagation' (3) → (1) the distance is unchanged; (2) no strict decrease; (3) a strict decrease, i.e. membership in A; reason: the propagation clauses are informal descriptions of these distance facts; the operational restriction of Algorithm 1 to A is Lemma 4.3
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.2, PDF p.5 = printed p.5 (with the definition of d^t(e'_x) in the preceding paragraph)

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.2 (PDF p. 5). In a distance-decreasing update of the arc `u → v`, with `d^t(e'_x)`
the least weight of a simple path from `s` to `x` through the updated arc (`viaDist`):
(1) a vertex not reachable from `v` keeps its distance; (2) a vertex reachable from `v` with
`d^t(e'_x) ≥ d^{t-1}_x` has no strict distance decrease; (3) a vertex reachable from `v` with
`d^t(e'_x) < d^{t-1}_x` has a strict decrease, i.e. lies in the affected region. -/
theorem lemma_4_2 {n : ℕ} (G G' : WDigraph n) (s u v : Fin n)
    (hupd : IsDecreasingUpdate G G' u v) :
    (∀ x, ¬ G'.Reach v x → G'.dist s x = G.dist s x) ∧
    (∀ x, G'.Reach v x → G.dist s x ≤ G'.viaDist s u v x → ¬ G'.dist s x < G.dist s x) ∧
    (∀ x, G'.Reach v x → G'.viaDist s u v x < G.dist s x → G'.dist s x < G.dist s x) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
