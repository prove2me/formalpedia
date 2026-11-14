-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_iid_stopped_prefix_independent
-- name    : CountingLLL.ContractedWalk.iid_stopped_prefix_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:51:33.497589+00:00
-- url     : https://prove2.me/theorems/c288a6ca-0895-44e8-935c-8278baa2564e
-- title:
--   Stopped-prefix information is independent of the IID tail
-- statement:
--   Let $\tau$ be a finite stopping index on an IID Bernoulli tape, with $\{\tau=n\}$ determined by the bits before $n$. Let a natural-valued variable $R$ also be determined by those stopped bits. Then $R$ is independent of the shifted tape beginning at $\tau$. This is the strong-Markov independence ingredient for splitting the contracted walk into first-hit segments.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.iid_stopped_prefix_independent (p : ℝ≥0∞) (hp : p ≤ 1) (τ R : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = n ↔ τ ω' = n))
    (hR : ∀ n ω ω', (∀ k < n, ω k = ω' k) → τ ω = n → R ω = R ω') :
    IndepFun R (fun ω k => ω (k+τ ω)) (tapeLaw p) := by sorry
