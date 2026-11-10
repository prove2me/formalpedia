-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_path_collision
-- name    : FlowOptimalSeparators.MinorFree.path_collision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:16.354812+00:00
-- url     : https://prove2.me/theorems/24f05f3c-e351-48f6-9466-3cb0324b1249
-- title:
--   Proposition 2 — independent endpoint-path collision
-- statement:
--   Let $h\ge3$, let $G$ be $K_h$-minor-free, and let $\pi$ be any probability distribution on its vertices. Independently sample two endpoints from $\pi$, then sample a simple path from their fixed conditional path law, using the singleton path when the endpoints agree. For two independent paths $P,P'$, the proof's choice $c_0=1/2500$ gives
--   $$\Pr[V(P)\cap V(P')\ne\varnothing]\ge\frac1{2500h^2}.$$
--   The conditional laws must normalize for every positive-mass endpoint pair; disconnected supported pairs cannot be represented by a zero law. This result supplies the path-collision obstruction for minor-free graphs.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - encoding: an absolute c₀>0 → c₀=1/2500; reason: the proof on p.18 explicitly supplies this choice
--   - encoding: independent endpoint and conditional path samples → normalized finite vectors and finite sums over simple paths; reason: finite sums give the same probability, including arbitrary endpoint laws and diagonal singletons
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 17–18, Proposition 2

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Proposition 2, pp.17-18: the proof supplies c₀ = 1/2500. The supported-pair kernel
is normalized, so nonexistent paths in a disconnected graph do not become a zero law. -/
theorem path_collision {n : ℕ} (G : Graph n) (h : ℕ) (hh : 3 ≤ h)
    (hG : ExcludesClique G h) (π : Fin n → ℝ) (hπ : EndpointLaw π)
    (κ : Fin n → Fin n → List (Fin n) → ℝ) (hκ : PathKernel G π κ) :
    (1 : ℝ) / (2500 * (h : ℝ) ^ 2) ≤ collisionProbability π κ := by sorry

end FlowOptimalSeparators.MinorFree
