-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_variance_counter
-- name    : AdaptiveRefresh.Main.variance_counter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:32.091024+00:00
-- url     : https://prove2.me/theorems/9741ef93-989b-4980-b820-358679e7b1a9
-- title:
--   Lemma 4.5 — variance from exact counters
-- statement:
--   At every analytical step, for every vertex $v$, the diagonal adjacency variance and exact counters obey
--
--   $$V_{vv}\le\frac1p(a_v+\Delta).$$
--
--   The statement includes Algorithm 4's exact counters and the analysis-only true counters $a'_v$ of the fast process, whose reset and increment identities are identical. This bounds variance without assuming that either counter process stays small.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
--   - generalization: Algorithm 4 exact counters a_v → both Algorithm 4 and the fast process analysis-only true counters; reason: §4.3.3 explicitly states that the same update identity gives the bound for the true counters; exact=true specializes to Lemma 4.5
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.5, printed p. 10 (PDF p. 11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem variance_counter (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (exact : Bool) (ω : ℕ → ℝ)
    (i : ℕ) (v : Fin n) :
    (refreshRun n G η t exact S ω i).variance v ≤
      (samplingRate η (initialMaxDegree n G) G.length)⁻¹ *
        ((refreshRun n G η t exact S ω i).trueCounter v + initialMaxDegree n G) := by sorry

end AdaptiveRefresh.Main
