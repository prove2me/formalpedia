-- Prove2me | Theorems.Thm_BeyondDS_Supplement_theorem_5
-- name    : BeyondDS.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:11:30.657608+00:00
-- url     : https://prove2.me/theorems/e86f9c0c-5031-4f83-8733-857cd2601e57
-- title:
--   Theorem 5 — at $n=2f+1$ with arbitrary correlated setup, CSU error $\eta<1/3$ forces $(f+1)(1-3\eta)/2$ expected senders, and $(n^2-1)(1-3\eta)/4$ expected messages for multicast protocols
-- statement:
--   Let $n=2f+1$ with $f\ge1$. Consider any protocol with binary inputs, point-to-point messages, and an arbitrary input-independent correlated initial setup whose distribution is unchanged by passive corruptions, run under any fixed delivery schedule. Suppose it solves consensus with strong unanimity with error at most $\eta<1/3$: for every set $F$ of at most $f$ passively corrupt players and every input assignment, with probability at least $1-\eta$ all honest players decide, their decisions agree, and equal honest inputs force that input as the decision.
--
--   1. There are a corrupt set $F$ with $|F|\le f$ and an input assignment whose execution has
--   $$\mathbb E[M]\;\ge\;\frac{(f+1)(1-3\eta)}{2},$$
--   where $M$ is the number of distinct honest senders.
--   2. If every send is a multicast, there are such $F$ and inputs whose execution has
--   $$\mathbb E[K]\;\ge\;\frac{(n^2-1)(1-3\eta)}{4},$$
--   where $K$ is the number of point-to-point messages sent by honest players.
--
--   So constant error below $1/3$ needs linearly many distinct senders, and quadratic communication for multicast protocols, whatever the setup.
--
--   **Formalization Note** The protocol class is `LocalProtocol`: one probability space for the setup and all tapes, deterministic local machines, unbounded executions. Senders and messages are counted over the whole execution, after decisions included. Expectations are integrals in $[0,\infty]$, and `MeasurableRun` is the standing measurability convention.
--
--   Differences from the source:
--   - generalization: error at most η for every permitted adversary corrupting at most f players → error at most η is assumed only for static passive corruptions of at most f players; reason: every class of permitted adversaries contains them, so the hypothesis is weaker
--   - reading: "has an execution distribution with at least (f + 1)(1 − 3η)/2 expected distinct honest senders" and "its worst-case expected message complexity is at least (n² − 1)(1 − 3η)/4" → ∃ a static passive corrupt set of size ≤ f and an input assignment whose execution attains each bound; reason: this is the form Corollary 12.1 and (77) prove: "some execution with a static passive adversary, possibly with no corruptions, attains at least this expected sender count"
--   - generalization: private tapes independent of inputs and setup; one fixed permitted delivery schedule → the tapes are part of one input-independent sample with no independence required; the statement holds for every fixed delivery schedule; reason: the proof couples executions on one probability space and uses no independence
--   - encoding: executions in continuous or round-based time; expectations → discrete steps with a delay function; lower integrals in [0, ∞]; a measurability convention on the run; reason: Lean conventions; same instances
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 5, p.5 (PDF p.6); §12, pp.57–59 (PDF pp.58–60): model, Corollary 12.1, eq. (77)

import Mathlib
import Definitions.Def_BeyondDS_Supplement_LocalProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BeyondDS.Supplement

/-- Theorem 5 (Tight majority with arbitrary initial setup), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.5 (PDF 6): "For n = 2f + 1 and f ≥ 1, any consensus protocol with strong unanimity and error at most η < 1/3 has an execution distribution with at least (f + 1)(1 − 3η)/2 expected distinct honest senders, even with arbitrary input-independent correlated initial setup whose distribution is unchanged by passive corruptions. If every honest send is a multicast, its worst-case expected message complexity is at least (n² − 1)(1 − 3η)/4." Proof: §12, Corollary 12.1 and (77), p.59 (PDF 60).

Let `n = 2f + 1` with `f ≥ 1`, and let `P` be a protocol of the local model (`LocalProtocol`: arbitrary input-independent joint setup, point-to-point messages, unbounded executions), run under a fixed delivery schedule `delay`, whose CSU error is at most `η < 1/3` against every static passive corruption of at most `f` players. Then

1. there are a corrupt set `F` with `|F| ≤ f` and an input assignment `x` whose execution has expected number of distinct honest senders `E[M] ≥ (f + 1)(1 − 3η)/2`;
2. if every send is a multicast, there are `F`, `|F| ≤ f`, and `x` whose execution has expected number of honest point-to-point messages `E[K] ≥ (n² − 1)(1 − 3η)/4`.

**Formalization Note.** The hypothesis is required only of the static passive adversaries, which every class of permitted adversaries contains, and the conclusions exhibit executions with such adversaries, as Corollary 12.1 does ("some execution with a static passive adversary, possibly with no corruptions, attains at least this expected sender count"). Expectations are lower Lebesgue integrals in `[0, ∞]`. `MeasurableRun` is the standing measurability convention. -/
theorem theorem_5 (f : ℕ) (hf : 1 ≤ f) (P : LocalProtocol (2 * f + 1) Bool)
    (delay : ℕ → Fin (2 * f + 1) → Fin (2 * f + 1) → ℕ) (hP : P.MeasurableRun delay)
    (η : ℝ) (hη : η < 1 / 3) (herr : P.CSUErrorLE delay f η) :
    (∃ F : Finset (Fin (2 * f + 1)), F.card ≤ f ∧ ∃ x : Fin (2 * f + 1) → Bool,
      ENNReal.ofReal (((f : ℝ) + 1) * (1 - 3 * η) / 2) ≤
        ∫⁻ ω, (P.numSenders delay F x ω : ℝ≥0∞) ∂P.μ) ∧
    (P.IsMulticast delay →
      ∃ F : Finset (Fin (2 * f + 1)), F.card ≤ f ∧ ∃ x : Fin (2 * f + 1) → Bool,
        ENNReal.ofReal ((((2 * f + 1 : ℕ) : ℝ) ^ 2 - 1) * (1 - 3 * η) / 4) ≤
          ∫⁻ ω, P.numMsgs delay F x ω ∂P.μ) := by sorry

end BeyondDS.Supplement
