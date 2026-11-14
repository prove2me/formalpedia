-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_iid_ae_strong_markov
-- name    : CountingLLL.ContractedWalk.iid_ae_strong_markov
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:54:28.655587+00:00
-- url     : https://prove2.me/theorems/14ddfab3-3580-49bc-a303-b5ca2bfaffc2
-- title:
--   IID strong Markov property at an almost-surely finite stopping time
-- statement:
--   Let an IID Bernoulli tape have an Option-valued stopping time $\tau$ that is finite almost surely, with each event $\{\tau=n\}$ determined by the first $n$ bits. If a natural-valued random variable is determined by the stopped prefix, then it is independent of the post-$\tau$ tape, and that tape has the original IID law. The null nonstopping event uses a fixed fallback. This strong-Markov property supports the source’s first-hit segmentation.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.iid_ae_strong_markov (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → Option ℕ) (R : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = some n ↔ τ ω' = some n))
    (hR : ∀ n ω ω', (∀ k < n, ω k = ω' k) → τ ω = some n → R ω = R ω')
    (hfin : ∀ᵐ ω ∂tapeLaw p, τ ω ≠ none) :
    IndepFun R (fun ω k => ω (k+(τ ω).getD 0)) (tapeLaw p) ∧
    (∀ A : Set Tape, MeasurableSet A → tapeLaw p ((fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) ⁻¹' A) = tapeLaw p A) := by sorry
