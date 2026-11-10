-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_termination_steps
-- name    : AdaptiveRefresh.Main.termination_steps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:29.91736+00:00
-- url     : https://prove2.me/theorems/44adf670-8015-48a3-9a7d-9876c82e8d3a
-- title:
--   Lemma 4.3 — termination in analytical steps
-- statement:
--   Consider the complete decremental execution, with at most $m$ live identities available for deletion initially. With probability at least $1-m^{-10}$, the algorithm has terminated by
--
--   $$8m^2$$
--
--   analytical steps. Initialization contributes one edge-sampling step per edge and a refresh contributes one contraction and one sample per current incident identity. These are the analytical steps used by the concentration proof, not RAM operations.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.3, printed p. 9 (PDF p. 10). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem termination_steps (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 10) ≤ tapeLaw {ω |
      (refreshRun n G η t false S ω (8 * G.length ^ 2)).stopped = true} := by sorry

end AdaptiveRefresh.Main
