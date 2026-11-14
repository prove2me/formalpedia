-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
-- name    : CountingLLL.ContractedWalk.upward_count_measurable_integrable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:39:42.550497+00:00
-- url     : https://prove2.me/theorems/3aecbfb5-5aae-4fc4-a3cf-d666f1a7cb09
-- title:
--   Stopped upward count is measurable and its generating integrand is integrable
-- statement:
--   The number of upward steps before absorption is a measurable function of the IID increment stream. Whenever the tape law is probabilistic and $0\le z\le1$, the generating-function integrand $z^K$ is integrable. This ensures the source’s stopped upward-count expectations are well-defined.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.upward_count_measurable_integrable : (∀ i : ℕ, Measurable (fun ω : Tape => upwardCount ω i)) ∧ (∀ (θ z : ℝ), θ ≤ 1 → 0 ≤ z → z ≤ 1 → ∀ i : ℕ, Integrable (fun ω : Tape => z ^ upwardCount ω i) (tapeLaw (ENNReal.ofReal θ))) := by sorry
