-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_adjacency_error
-- name    : AdaptiveRefresh.Main.adjacency_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:34.267288+00:00
-- url     : https://prove2.me/theorems/d94f5d15-0918-47ee-9502-49f042fea518
-- title:
--   Lemma 4.10 — adjacency error
-- statement:
--   With probability at least $1-m^{-9}$, every analytical step of the fast algorithm satisfies
--
--   $$\|A_H-A_G\|\le\tfrac12\eta\Delta.$$
--
--   Here $G$ is the transient graph at that step: a contraction temporarily removes incident identities before they are restored one at a time. This scope includes initialization and incomplete refreshes.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.10, printed p. 12 (PDF p. 13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem adjacency_error (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 9) ≤ tapeLaw {ω | ∀ i : ℕ,
      opNorm (adjacencyError (refreshRun n G η t false S ω i)) ≤ η * initialMaxDegree n G / 2} := by sorry

end AdaptiveRefresh.Main
