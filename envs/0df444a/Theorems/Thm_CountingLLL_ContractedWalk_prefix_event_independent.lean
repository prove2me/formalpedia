-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_prefix_event_independent
-- name    : CountingLLL.ContractedWalk.prefix_event_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:50:40.373879+00:00
-- url     : https://prove2.me/theorems/b26d090f-c719-4970-8d46-0dfb962ebdfe
-- title:
--   Fresh walk increment is independent of every prefix event
-- statement:
--   Let $\omega$ be an independent Bernoulli tape with success probability $p\le1$. If an event $E$ is completely determined by the coordinates before time $t$, then $$\Pr(E\cap\{\omega_t=1\})=\Pr(E)\,p.$$ This allows current walk level and accumulated counter to be used together when analyzing the next fresh upward step.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.prefix_event_independent (p : ℝ≥0∞) (hp : p ≤ 1) (t : ℕ) (E : Set Tape)
    (hE : ∀ ω ω', (∀ k < t, ω k = ω' k) → (ω ∈ E ↔ ω' ∈ E)) :
    tapeLaw p {ω | ω ∈ E ∧ ω t = true} = tapeLaw p E * p := by sorry
