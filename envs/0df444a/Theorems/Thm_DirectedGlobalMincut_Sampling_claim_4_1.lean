-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_claim_4_1
-- name    : DirectedGlobalMincut.Sampling.claim_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:35.19728+00:00
-- url     : https://prove2.me/theorems/5de91ded-9b4e-4530-97ad-e3a7c52cc343
-- title:
--   Claim 4.1 — Demand-satisfying flows give connectivity two
-- statement:
--   Let $T$ be a spanning out-arborescence rooted at $r$. Let $g_0$ be any nonnegative demand-satisfying flow in the warmup auxiliary network, and let $h=g_0|_E$ be its projection. No capacity restriction is imposed on $g_0$. For every nonempty vertex set $S$ excluding the root,
--
--   $$(1_T+h)(\delta^-(S))\ge2.$$
--
--   This remains applicable to rounded flows that cross a fractional auxiliary capacity. The projected vector is not required to be a circulation or a flow obeying the original graph's weight capacities.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n vertices and an ambient Fin m arc type, with G.arcs selecting the active identities; reason: all source graphs have an exhaustive enumeration; unused ambient identifiers have zero incidence and zero auxiliary projection, so permitting them changes no active graph or cut
--   - encoding: a_e=(s_v,y_e) for every e=(u,v), although s_r is not defined on p.5 → omit source arcs entering r and project those original arcs to zero; reason: every rooted out-arborescence already has zero incidence on these arcs; the two-vertex opposite-arcs graph demonstrates the undefined source symbol
--   - generalization: the section fixes nonnegative q and the input graph of section 1 → all finite arc-identity graphs with the stated tree, and arbitrary irrelevant q in the capacity-free assertion; reason: capacity values are never consulted by DemandFlow, and the proof uses neither graph weights nor the section 1 size bounds
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Claim 4.1, p. 6 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Flows

namespace DirectedGlobalMincut.Sampling

/-- Claim 4.1 (p.6). No capacity bound is assumed on the demand-satisfying flow. -/
theorem claim_4_1 {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (hT : IsTree G r T) (q : Fin m → ℝ)
    (g : (WarmNode r T × WarmNode r T) → ℝ)
    (hg : DemandFlow (warmNetwork G r T q) g) :
    ∀ S, IsRootedCut r S →
      2 ≤ cutWeight G (fun e => incidence T e + warmProjection G r T g e) S := by sorry

end DirectedGlobalMincut.Sampling
