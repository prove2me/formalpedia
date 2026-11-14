-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_iid_ae_stopped_prefix_independent
-- name    : CountingLLL.ContractedWalk.iid_ae_stopped_prefix_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:53:42.052515+00:00
-- url     : https://prove2.me/theorems/f3eff2c9-ea34-4b9f-b7ba-3e90f2784f43
-- title:
--   Stopped-prefix independence for an almost-surely finite IID stopping time
-- statement:
--   Let an IID Bernoulli tape have an Option-valued stopping time $\tau$ that is finite almost surely, with each event $\{\tau=n\}$ determined by the first $n$ bits. Let a natural-valued random variable be determined by the stopped prefix. Then that variable is independent of the post-$\tau$ increment tape. On the null nonstopping event the shifted tape uses an arbitrary fixed fallback. This gives the strong-Markov independence needed for first-hit segmentation.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.iid_ae_stopped_prefix_independent (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → Option ℕ) (R : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = some n ↔ τ ω' = some n))
    (hR : ∀ n ω ω', (∀ k < n, ω k = ω' k) → τ ω = some n → R ω = R ω')
    (hfin : ∀ᵐ ω ∂tapeLaw p, τ ω ≠ none) :
    IndepFun R (fun ω k => ω (k+(τ ω).getD 0)) (tapeLaw p) := by sorry
