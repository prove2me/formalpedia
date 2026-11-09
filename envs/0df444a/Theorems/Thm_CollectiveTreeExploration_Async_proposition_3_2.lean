-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_proposition_3_2
-- name    : CollectiveTreeExploration.Async.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:09.452076+00:00
-- url     : https://prove2.me/theorems/3fbfa9b5-9cde-43ea-a230-e815c11c079f
-- title:
--   Proposition 3.2 — the CTM strategy is well defined, keeps (I), and C_x ≤ 128 C_y
-- statement:
--   Let $k\ge2$ and consider the CTM strategy $x(t)$ of §3.1 (repair, fork and deletion rules). Along every play of the continuous tree-mining game:
--   1. the strategy is well defined: every response is a legal integral configuration, so its cumulative cost is finite;
--   2. at all times the invariant (I) holds:
--   $$y_\ell\ge\tfrac12,\qquad x_\ell\ge1,\qquad x_\ell<y_\ell+\tfrac32\quad\text{at every leaf }\ell;$$
--   3. denoting by $C_x(t)$ and $C_y(t)$ the cumulative movement costs of $x(\cdot)$ and of the fractional minimizer $y(\cdot)$ up to time $t$,
--   $$C_x(t)\le128\,C_y(t).\tag{5}$$
--
--   The proposition reduces the analysis of the integral strategy to that of the fractional minimizer.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - reading: the fork length δ ∈ (0,1] is chosen sufficiently small (to preserve (I)) → δ is half the supremum of the lengths in (0,1] for which (I) holds for every child length in (0,δ], and 1 if there is none; ties are broken by smallest label; reason: the source leaves the choice open; this is one deterministic instance, and its admissibility is part of the claim
--   - encoding: at all times → in the initial state and after every event of every play (every finite prefix, including elongations stopped at any time); reason: prefixes of plays are plays
--   - encoding: the strategy is well-defined and C_x counts cumulative movement → WellFormedCTM for the induced response functions, and transfer-by-transfer costs including evacuation and repairs; no termination or invariant is assumed; reason: failed repairs give illegal responses and infinite cost, and blocking an elongation cannot hide an invalid plan
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Proposition 3.2, pp.7–8; strategy §3.1, p.7; proof in Appendix A, pp.15–16

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerStrategy

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Proposition 3.2** (pp.7–8; proof in Appendix A, pp.15–16). The CTM strategy of §3.1 is
well defined (every response is legal, so its cost is finite), enforces at all times the invariant
(I): `y_ℓ ≥ 1/2`, `x_ℓ ≥ 1`, `x_ℓ < y_ℓ + 3/2` at every leaf, and its cumulative cost satisfies
`C_x(t) ≤ 128 C_y(t)` (5). -/
theorem proposition_3_2 (k : ℕ) (hk : 2 ≤ k) (es : List Event) (recs : List StepRecord)
    (h : ctmRun (powerStrategy k) es = some recs) :
    WellFormedCTM (powerStrategy k) ∧
    playCost recs < ⊤ ∧
    (initState k).tree.InvI (initState k).x ((initState k).tree.fracMin k) ∧
    (∀ r ∈ recs, r.after.tree.InvI r.after.x (r.after.tree.fracMin k)) ∧
    playCost recs ≤ 128 * fracCost k recs := by sorry

end CollectiveTreeExploration.Async
