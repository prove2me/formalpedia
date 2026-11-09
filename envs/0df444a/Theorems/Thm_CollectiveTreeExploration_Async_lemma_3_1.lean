-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_1
-- name    : CollectiveTreeExploration.Async.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:15:43.694123+00:00
-- url     : https://prove2.me/theorems/1c6e0d1c-d1cf-44f8-a56e-7b3e44dc2fdf
-- title:
--   Lemma 3.1 — uniqueness, positivity and monotone differentiability of the fractional minimizer
-- statement:
--   Let $k\ge2$ and let $T$ be a game tree (positive non-root edge lengths, every non-root internal vertex with at least two children). Then:
--   1. Problem (4), $\min\{\Phi_T(y): y\ge0,\ \sum_\ell y_\ell=k\}$, has a unique minimizer $y$.
--   2. $y_\ell>0$ at every leaf $\ell$.
--   3. During the continuous elongation of a non-root leaf $l$, $y$ is differentiable with respect to the length $d_l$, and its derivative satisfies
--   $$\forall u\in l\to r:\ \dot y_u\le0,\qquad \forall u\notin l\to r:\ \dot y_u\ge0 .$$
--
--   The lemma makes the fractional minimizer $y(t)$ a well-defined, smoothly evolving object on which the whole analysis is built.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: during the continuous elongation of a leaf l, y(t) is differentiable → for every game tree and every non-root leaf l, y is differentiable in d_l at the current length (every instant of every elongation is such a tree); reason: unit-rate elongation makes the time derivative the derivative in d_l
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.1, p.7

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.1** (p.7). On a tree of the game, problem (4) has a unique minimizer `y`, with
`y_ℓ > 0` at every leaf. During the elongation of a non-root leaf `l`, `y` is differentiable in the
length `d_l`, with `ẏ_u ≤ 0` for `u ∈ l → r` and `ẏ_u ≥ 0` for every other vertex `u`. -/
theorem lemma_3_1 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) :
    (∃! y : ℕ → ℝ, T.IsFracMinimizer k y) ∧
    (∀ ℓ ∈ T.leaves, 0 < T.fracMin k ℓ) ∧
    ∀ l ∈ T.leaves, l ≠ T.root →
      (∀ v : ℕ, HasDerivAt (fun L : ℝ => (T.setLen l L).fracMin k v) (T.ydot k l v) (T.len l)) ∧
      (∀ u ∈ T.pathVerts l T.root, T.mass (T.ydot k l) u ≤ 0) ∧
      (∀ u ∈ T.V, u ∉ T.pathVerts l T.root → 0 ≤ T.mass (T.ydot k l) u) := by sorry

end CollectiveTreeExploration.Async
