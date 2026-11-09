-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_7
-- name    : CollectiveTreeExploration.Async.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:36.471696+00:00
-- url     : https://prove2.me/theorems/8304929f-89ef-4846-b192-6de2e020d22d
-- title:
--   Lemma 3.7 — voltage identity
-- statement:
--   Let $k\ge2$, $T$ a game tree with fractional minimizer $y$, $l$ a non-root leaf elongated at unit rate, and $V$ the voltage computed from the Dirichlet problem for network (8), with leaf voltages $V_l=y_l^\varepsilon/\varepsilon$, $V_\ell=0$ otherwise and Kirchhoff conservation at internal nodes. Then every vertex $v\succeq l$ satisfies
--   $$y_vV_v-h_v\dot y_v=y_lV_l,\tag{9}$$
--   and since $\dot y_v\le0$,
--   $$V_v\le\frac{y_l}{y_v}V_l .$$
--
--   The identity controls the voltage available to move mass into side branches.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: the voltage in the electrical network (8) → the chosen solution of the Dirichlet boundary problem with resistances rho_u/y_u and the prescribed leaf voltages, extended by zero outside the vertices; reason: constructs the network potential from its input data; no voltage identity or desired current is assumed
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.7, p.10

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.7** (voltage identity, p.10). In the network (8) of the elongation of the leaf `l`,
let `V` be the computed Dirichlet potential of network (8). Then every vertex
`v ⪰ l` satisfies `y_v V_v − h_v ẏ_v = y_l V_l` (9), and `V_v ≤ (y_l / y_v) V_l`. -/
theorem lemma_3_7 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root) :
    let V := T.networkVoltage k l
    ∀ v ∈ T.V, T.Desc l v →
      T.mass (T.fracMin k) v * V v - T.hgt k v * T.mass (T.ydot k l) v = T.fracMin k l * V l ∧
      V v ≤ T.fracMin k l / T.mass (T.fracMin k) v * V l := by sorry

end CollectiveTreeExploration.Async
