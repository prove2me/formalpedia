-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_upward_count_real_integrable
-- name    : CountingLLL.ContractedWalk.upward_count_real_integrable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:05:44.566212+00:00
-- url     : https://prove2.me/theorems/cecc61f0-0883-4744-9b3b-cc8638547643
-- title:
--   Number of upward contracted-walk changes is integrable
-- statement:
--   For a contracted walk with $0\leq\theta<1/3$ and any initial level, the total number of upward changes before absorption has finite expectation. The theorem asserts integrability of the real-valued count, enabling Fubini in the harmonic generating-function calculation.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.upward_count_real_integrable (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) (i : ℕ) :
    Integrable (fun ω : Tape => (upwardCount ω i : ℝ)) (tapeLaw (ENNReal.ofReal θ)) := by sorry
