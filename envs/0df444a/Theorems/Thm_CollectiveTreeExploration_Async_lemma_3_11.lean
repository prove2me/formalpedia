-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_11
-- name    : CollectiveTreeExploration.Async.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:28.801502+00:00
-- url     : https://prove2.me/theorems/6f9b9546-a557-4511-81fb-b75d9808509c
-- title:
--   Lemma 3.11 — upper bound on the movement at a deletion
-- statement:
--   Let $k\ge2$, $T$ a game tree and $l$ a non-root leaf of $T$ that is not the only leaf. Let $y(t^-)$ be the fractional minimizer on $T$ and $y(t^+)$ the one on the tree after the deletion of $l$. Suppose that $y_\ell(t^-)\ge\frac12$ at every leaf (the fractional part of (I), which holds for the specified strategy), and that $y_l=\frac12$ upon deletion. Then
--   $$\mathrm{OT}_d\bigl(y(t^-),y(t^+)\bigr)\le4d_l\bigl(\log(2k)+1\bigr),\tag{12}$$
--   the transport being measured with the edge lengths of the tree before the deletion.
--
--   With Lemma 3.10 this gives the Deletion Eq. of §3.4.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - generalization: deletion along the specified game strategy under invariant (I), with y_l = 1/2 → any positive game-shaped tree whose fractional minimizer has every leaf mass at least 1/2 and y_l = 1/2, independently of an integral configuration; reason: the proof on pp.12–13 uses only these fractional bounds; every source strategy state satisfies them, so all source instances are included
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.11, p.12; proof pp.12–13

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.11** (upper bound on the movement, p.12). In the deletion of a leaf `l` of a tree on
which the fractional minimizer satisfies `y_ℓ ≥ 1/2` at every leaf (part of (I)), assuming
`y_l = 1/2` upon deletion, `OT_d(y(t⁻), y(t⁺)) ≤ 4 d_l (log(2k) + 1)` (12), the transport being
measured in the tree before the deletion. -/
theorem lemma_3_11 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root) (hsurv : ∃ ℓ ∈ T.leaves, ℓ ≠ l)
    (hI : ∀ ℓ ∈ T.leaves, (1 / 2 : ℝ) ≤ T.fracMin k ℓ) (hhalf : T.fracMin k l = 1 / 2) :
    T.OT (T.fracMin k) ((T.delete l).fracMin k) ≤
      4 * T.len l * (Real.log (2 * (k : ℝ)) + 1) := by sorry

end CollectiveTreeExploration.Async
