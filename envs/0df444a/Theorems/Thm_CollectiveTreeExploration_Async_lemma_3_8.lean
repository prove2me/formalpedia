-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_8
-- name    : CollectiveTreeExploration.Async.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:09.242988+00:00
-- url     : https://prove2.me/theorems/e5a464b5-0c19-4eeb-a795-b9655bf96c50
-- title:
--   Lemma 3.8 — bounding movement by $y_l^p$
-- statement:
--   Let $k\ge2$, $T$ a game tree with fractional minimizer $y$, and $l$ a non-root leaf whose edge $(p_l,l)$ is elongated at unit rate. The instantaneous movement cost in the approximate edge length metric satisfies
--   $$\|\dot y\|_\rho\le\frac{2y_l^p}{\varepsilon}\log\Bigl(\frac{k}{y_l}\Bigr).\tag{E}$$
--
--   Together with $\dot\Phi=y_l^p$ this gives the Elongation Eq. of §3.3.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.8, p.10; proof p.11

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.8** (p.10). In a unit-rate elongation of the leaf edge `(p_l, l)`,
`‖ẏ‖_ρ ≤ (2 y_l^p / ε) log(k / y_l)` (E). -/
theorem lemma_3_8 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root) :
    T.rhoNormYdot k l ≤
      2 * T.fracMin k l ^ pexp k / eps k * Real.log (k / T.fracMin k l) := by sorry

end CollectiveTreeExploration.Async
