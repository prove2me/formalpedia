-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_9
-- name    : CollectiveTreeExploration.Async.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:04.804841+00:00
-- url     : https://prove2.me/theorems/5dd91b80-f8ef-497a-bc9f-813975af6944
-- title:
--   Lemma 3.9 — bounding movement by $\dot y_l$
-- statement:
--   Let $k\ge2$, $T$ a game tree with fractional minimizer $y$, and $l$ a non-root leaf elongated at unit rate. If $y_{p_l}\ge2y_l$, then
--   $$\|\dot y\|_\rho\le4\rho_l\,(-\dot y_l)\log\Bigl(\frac{k}{y_l}\Bigr).\tag{E'}$$
--
--   No invariant is assumed: the lemma is applied in the auxiliary elongation of Lemma 3.11, where the mass at the deleted leaf falls below $1/2$.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.9, p.11

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.9** (p.11). In an elongation of the leaf `l`, if `y_{p_l} ≥ 2 y_l`, then
`‖ẏ‖_ρ ≤ 4 ρ_l (−ẏ_l) log(k / y_l)` (E'). -/
theorem lemma_3_9 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root)
    (hpar : 2 * T.fracMin k l ≤ T.mass (T.fracMin k) (T.par l)) :
    T.rhoNormYdot k l ≤
      4 * T.rho k l * (-T.mass (T.ydot k l) l) * Real.log (k / T.fracMin k l) := by sorry

end CollectiveTreeExploration.Async
