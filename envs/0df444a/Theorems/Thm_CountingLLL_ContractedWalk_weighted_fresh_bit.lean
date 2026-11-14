-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_weighted_fresh_bit
-- name    : CountingLLL.ContractedWalk.weighted_fresh_bit
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:53:24.724914+00:00
-- url     : https://prove2.me/theorems/d235535f-2ca7-4ddc-b1c6-4f8bc3ea33fb
-- title:
--   Prefix-weighted probability of a fresh upward step
-- statement:
--   For an independent Bernoulli tape with success probability $p\le1$, let $W$ be any nonnegative weight determined by the first $t$ bits. Then $$\mathbb E[W\,\mathbf 1_{\{\omega_t=1\}}]=p\,\mathbb E[W].$$ The result includes arbitrary nonnegative, possibly unbounded weights and is suited to the weighted upward-change count in the source cost analysis.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.weighted_fresh_bit (p : ℝ≥0∞) (hp : p ≤ 1) (t : ℕ)
    (F : ((Finset.range t) → Bool) → ℝ≥0∞) :
    (∫⁻ ω : Tape, F (fun j => ω j) * (if ω t then 1 else 0) ∂tapeLaw p) =
      (∫⁻ ω : Tape, F (fun j => ω j) ∂tapeLaw p) * p := by sorry
