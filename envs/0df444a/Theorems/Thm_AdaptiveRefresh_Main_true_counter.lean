-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_true_counter
-- name    : AdaptiveRefresh.Main.true_counter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:23.551392+00:00
-- url     : https://prove2.me/theorems/b626d13a-2c5d-407b-b8a1-dd4052d25de3
-- title:
--   Lemma 4.9 — true counters
-- statement:
--   With probability at least $1-m^{-10}$, simultaneously at every analytical step before completion of the first $2m+3$ refreshes and every vertex $v$,
--
--   $$a'_v<9\Delta+42\Delta\log m<43\Delta\log m.$$
--
--   Both strict inequalities are included. The true counters are defined by their exact updates, and their bound is a conclusion.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.9, printed p. 12 (PDF p. 13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem true_counter (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 10) ≤ tapeLaw {ω | ∀ i : ℕ,
      BeforeRefreshHorizon G.length (refreshRun n G η t false S ω i) →
      (∀ v : Fin n, (refreshRun n G η t false S ω i).trueCounter v <
        9 * initialMaxDegree n G + 42 * initialMaxDegree n G * Real.log G.length) ∧
      9 * initialMaxDegree n G + 42 * initialMaxDegree n G * Real.log G.length <
        43 * initialMaxDegree n G * Real.log G.length} := by sorry

end AdaptiveRefresh.Main
