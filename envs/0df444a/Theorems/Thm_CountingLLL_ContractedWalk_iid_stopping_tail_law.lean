-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_iid_stopping_tail_law
-- name    : CountingLLL.ContractedWalk.iid_stopping_tail_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:49:37.897195+00:00
-- url     : https://prove2.me/theorems/d0fbf0e1-822c-4e27-b81d-151bfb000f0f
-- title:
--   IID increments retain their law after a finite stopping time
-- statement:
--   Let $\tau$ be a finite index on an IID Bernoulli increment stream such that the event $\{\tau=n\}$ is determined by bits strictly before $n$. The shifted stream beginning at $\tau$ has the same IID product law as the original stream. This is a stopping-time tail-law ingredient for the first-hit decomposition in Lemma 6.5.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.iid_stopping_tail_law (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = n ↔ τ ω' = n)) :
    (tapeLaw p).map (fun ω k => ω (k+τ ω)) = tapeLaw p := by sorry
