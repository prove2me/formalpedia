-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_counter_error
-- name    : AdaptiveRefresh.Main.counter_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:38.775881+00:00
-- url     : https://prove2.me/theorems/d7ba0672-c430-43e0-b5a1-30d1c5f6ee06
-- title:
--   Lemma 4.8 — counter estimation error
-- statement:
--   Let $E'_i=\operatorname{diag}(a'_i-\widehat a_i)$. With probability at least $1-m^{-10}$, simultaneously at every analytical step before completion of the first $2m+3$ refreshes,
--
--   $$\|E'_i\|\le42\Delta\log m.$$
--
--   The event is stated on the actual execution's stopped horizon. It is not conditional on a refresh-count or true-counter success event.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.8, printed p. 11 (PDF p. 12). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem counter_error (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 10) ≤ tapeLaw {ω | ∀ i : ℕ,
      BeforeRefreshHorizon G.length (refreshRun n G η t false S ω i) →
      opNorm (counterError (refreshRun n G η t false S ω i)) ≤
        42 * initialMaxDegree n G * Real.log G.length} := by sorry

end AdaptiveRefresh.Main
