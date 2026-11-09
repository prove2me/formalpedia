-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_claim_4_2
-- name    : DirectedGlobalMincut.Sampling.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:06.319074+00:00
-- url     : https://prove2.me/theorems/e0a1f954-760d-4265-a401-ce90b5ce680a
-- title:
--   Claim 4.2 — Feasibility
-- statement:
--   Let $T$ be a spanning out-arborescence rooted at $r$, and let $x\in A_r$ and $q\ge0$ satisfy $x\le q$ coordinatewise. The warmup auxiliary network has a nonnegative capacity-feasible flow $g_0$ satisfying its specified integer demands and the prescribed projection:
--
--   $$g_0|_E=x.$$
--
--   The assertion applies to each specified point $x$, rather than choosing a different dominated point. It is the feasibility input for the auxiliary maximum-flow computation.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n vertices and an ambient Fin m arc type, with G.arcs selecting the active identities; reason: all source graphs have an exhaustive enumeration; unused ambient identifiers have zero incidence and zero auxiliary projection, so permitting them changes no active graph or cut
--   - encoding: a_e=(s_v,y_e) for every e=(u,v), although s_r is not defined on p.5 → omit source arcs entering r and project those original arcs to zero; reason: every rooted out-arborescence already has zero incidence on these arcs; the two-vertex opposite-arcs graph demonstrates the undefined source symbol
--   - generalization: G subject to the global input restrictions of section 1 → the structural assertion on any finite arc-identity digraph with a spanning out-arborescence; reason: the displayed assertions and their source proofs do not use weights, polynomial bounds or m>=n; all original instances are included
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Claim 4.2, p. 7 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Flows

namespace DirectedGlobalMincut.Sampling

/-- Claim 4.2 (p.7): every prescribed dominated point lifts with that exact projection. -/
theorem claim_4_2 {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (hT : IsTree G r T) (q x : Fin m → ℝ) (hq : ∀ e, 0 ≤ q e)
    (hx : x ∈ arborescencePolytope G r) (hdom : ∀ e, x e ≤ q e) :
    ∃ g, FeasibleFlow (warmNetwork G r T q) g ∧ warmProjection G r T g = x := by sorry

end DirectedGlobalMincut.Sampling
