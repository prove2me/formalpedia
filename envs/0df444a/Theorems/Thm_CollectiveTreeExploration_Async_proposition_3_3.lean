-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_proposition_3_3
-- name    : CollectiveTreeExploration.Async.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:28.316581+00:00
-- url     : https://prove2.me/theorems/234042a4-3f35-436d-933a-ef1c16cab3c0
-- title:
--   Proposition 3.3 — the movement of the fractional minimizer is bounded by the potential
-- statement:
--   Let $k\ge2$, $\varepsilon=\log(4/3)/\log(2k)$, and write $\Phi(t)=\Phi_{T(t)}(y(t))$. Along every play of the CTM strategy of §3.1, the following inequality remains true at all times:
--   $$C_y(t)\le\frac{32\log(2k)}{\varepsilon}\,\Phi(t).\tag{6}$$
--
--   This is the paper's main technical result. Combined with Proposition 3.2 and $\Phi(t)\le k^pD\le2kD$ it gives Theorem 2.2.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: at all times → at the end of every play (every finite prefix, including elongations stopped at any time); reason: prefixes of plays are plays
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Proposition 3.3, p.8; proof §3.3–3.5, pp.9–13

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerStrategy

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Proposition 3.3** (p.8). Along every play of the CTM strategy of §3.1, at all times
`C_y(t) ≤ (32 log(2k) / ε) Φ(t)` (6), where `Φ(t) = Φ_{T(t)}(y(t))`. -/
theorem proposition_3_3 (k : ℕ) (hk : 2 ≤ k) (es : List Event) (recs : List StepRecord)
    (h : ctmRun (powerStrategy k) es = some recs) :
    fracCost k recs ≤ ENNReal.ofReal (32 * Real.log (2 * (k : ℝ)) / eps k *
      (finalState k recs).tree.Phi k ((finalState k recs).tree.fracMin k)) := by sorry

end CollectiveTreeExploration.Async
