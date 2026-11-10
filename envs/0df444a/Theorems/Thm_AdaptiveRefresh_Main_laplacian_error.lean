-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_laplacian_error
-- name    : AdaptiveRefresh.Main.laplacian_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:03:17.018096+00:00
-- url     : https://prove2.me/theorems/97201906-dfbf-4f3f-9e77-76bf4b6284c4
-- title:
--   Corollary 4.11 — Laplacian error
-- statement:
--   With probability at least $1-m^{-9}$, initialization and the delivered decremental interaction terminate, and the initial completed sparsifier and every completed deletion satisfy
--
--   $$\|L_H-L_G\|\le\eta\Delta.$$
--
--   These states have exhausted both repair queues and the sampling queue. The common event includes a termination certificate within the source's $8m^2$ analytical-step bound.
--
--   Differences from the source:
--   - reading: accuracy specified only by an upper bound → positive accuracy below one half; reason: accuracy is implicitly positive in the sampling probability and inverse-accuracy asymptotics
--   - encoding: the connected nontrivial unclipped sampling analysis of §4.1 → SamplingContext on Fin n with initial m equal to the number of edge identities; reason: the headline and additive algorithm theorems separately cover all sizes; this is exactly the supporting analysis regime
--   - encoding: randomness-adaptive edge deletions and fresh independent draws → causal history strategies with sequential draws; deterministic items quantify over every strategy and tape; reason: the deterministic invariants concern every execution and require no measurability; probability bounds use measurable strategies and independent uniform draws, with randomized adversaries covered by conditioning
--   - encoding: arbitrary deterministic choices of eligible vertices and mandatory endpoints → least-labelled eligible vertices, maximum counter priority, and the first recorded endpoint; reason: these fix only the deterministic tie breaks allowed by Algorithms 2–3
--   - encoding: a vertex refresh and its completion → the refresh count increases at its contraction, with the pending queue marking completion; reason: this preserves both total refresh counts and the before-completion scope of Lemmas 4.8–4.9
--   - encoding: an execution and its analytical steps → zero-indexed recursively defined states with stationary padding; an input stop is signalled by one identity transition; reason: each active step is exactly one edge sample or contraction; the identity transition leaves every bound unchanged and the nontrivial regime has slack in 8m²
--   - generalization: accuracy for the initial sparsifier and after each completed deletion → accuracy together with termination within 8m² steps on the same 1-m^-9 event; reason: the proof bounds the union of three m^-10 bad events in Lemma 4.10, including refresh-count failure; the 8m² conclusion follows on that event and leaves room in m^-9
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Corollary 4.11, printed p. 13 (PDF p. 14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_RefreshProcess

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

theorem laplacian_error (n : ℕ) (G : Graph) (η : ℝ) (t : ℕ)
    (hctx : SamplingContext n G η) (S : Strategy) (hS : Measurable S) :
    ENNReal.ofReal (1 - (G.length : ℝ)⁻¹ ^ 9) ≤ tapeLaw {ω |
      (refreshRun n G η t false S ω (8 * G.length ^ 2)).stopped = true ∧
      ∀ i : ℕ, Completed η (initialMaxDegree n G) false (refreshRun n G η t false S ω i) →
        opNorm (laplacian n (refreshRun n G η t false S ω i).H - laplacian n (refreshRun n G η t false S ω i).live) ≤
          η * initialMaxDegree n G} := by sorry

end AdaptiveRefresh.Main
