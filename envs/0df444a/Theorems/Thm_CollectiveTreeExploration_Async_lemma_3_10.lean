-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_10
-- name    : CollectiveTreeExploration.Async.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:45.210325+00:00
-- url     : https://prove2.me/theorems/f5f61943-2460-4354-a7ad-2d5357118a4c
-- title:
--   Lemma 3.10 — lower bound on the energy increase at a deletion
-- statement:
--   Let $k\ge2$, $T$ a game tree and $l$ a non-root leaf of $T$ that is not the only leaf. Let $y(t^-)$ be the fractional minimizer on $T$ and $y(t^+)$ the one on the tree after the deletion of $l$ (with suppression of a degree-two parent), and $\Delta\Phi=\Phi(t^+)-\Phi(t^-)$. Then
--   $$\Delta\Phi\ge\varepsilon\,d_l\,y_l(t^-)^p.\tag{11}$$
--
--   The potential gain pays for deletion-induced fractional transport in Proposition 3.3. The pre-deletion mass is unrestricted.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: the deletion of a leaf l → the tree after deleting l and suppressing its parent if it becomes a non-root vertex with one child; Φ(t⁺) computed on that tree; reason: the deletion operation of §2.2
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.10, p.12

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.10** (lower bound on the energy increase, p.12). In the deletion of a leaf `l`,
`ΔΦ = Φ(t⁺) − Φ(t⁻) ≥ ε d_l y_l(t⁻)^p` (11). -/
theorem lemma_3_10 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root) (hsurv : ∃ ℓ ∈ T.leaves, ℓ ≠ l) :
    eps k * T.len l * T.fracMin k l ^ pexp k ≤
      (T.delete l).Phi k ((T.delete l).fracMin k) - T.Phi k (T.fracMin k) := by sorry

end CollectiveTreeExploration.Async
