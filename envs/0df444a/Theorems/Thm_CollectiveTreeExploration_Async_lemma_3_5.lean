-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_5
-- name    : CollectiveTreeExploration.Async.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:24.63255+00:00
-- url     : https://prove2.me/theorems/0ad55bc9-ada0-495f-874a-ac1f1f1a2021
-- title:
--   Lemma 3.5 — relative depths of leaves
-- statement:
--   Let $k\ge2$, $T$ a game tree and $y$ its fractional minimizer, and assume (I) for some integral configuration $x$. Then for every vertex $v$ and any two distinct leaves $\ell,\ell'\preceq v$,
--   $$\frac{d(v,\ell')}{d(v,\ell)}\le\frac43.\tag{7}$$
--
--   Under the invariant, the leaves below a common vertex are at comparable depths; this bounds the cost of repairs and evacuations.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: under (I) → an integral configuration x of total mass k, with the three explicit leaf inequalities (I); reason: (I) is a property of the pair (x, y)
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.5, p.9

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.5** (p.9). Under (I), for every vertex `v` and any two distinct leaves `ℓ, ℓ' ⪯ v`,
`d(v, ℓ') / d(v, ℓ) ≤ 4/3` (7). -/
theorem lemma_3_5 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (x : ℕ → ℕ)
    (hx : T.IsIntConfig k x) (hI : T.InvI x (T.fracMin k)) :
    ∀ v ∈ T.V, ∀ ℓ ∈ T.leavesBelow v, ∀ ℓ' ∈ T.leavesBelow v, ℓ ≠ ℓ' →
      T.dist ℓ' v / T.dist ℓ v ≤ 4 / 3 := by sorry

end CollectiveTreeExploration.Async
