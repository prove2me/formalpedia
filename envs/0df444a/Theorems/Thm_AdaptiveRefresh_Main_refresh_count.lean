-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_refresh_count
-- name    : AdaptiveRefresh.Main.refresh_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:37.282239+00:00
-- url     : https://prove2.me/theorems/f140764d-0996-4316-9137-11690796b479
-- title:
--   Lemma 4.2 — total vertex refreshes
-- statement:
--   Let the fast algorithm face at most $t$ legal adaptive edge deletions. Over its own independent draws, with probability at least $1-m^{-10}$, every prefix of this execution satisfies
--
--   $$r_i<2t+3.$$
--
--   Initialization repairs are included. This event bounds the total number of refreshes, including any execution that fails to terminate; termination is not assumed.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.2, printed p. 8 (PDF p. 9). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem refresh_count (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 10) ≤ tapeLaw {ω | ∀ i : ℕ,
      (refreshRun n G η t false S ω i).refreshes < 2 * t + 3} := by sorry

end AdaptiveRefresh.Main
