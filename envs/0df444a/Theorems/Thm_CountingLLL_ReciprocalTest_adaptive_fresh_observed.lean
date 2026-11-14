-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_adaptive_fresh_observed
-- name    : CountingLLL.ReciprocalTest.adaptive_fresh_observed
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:36:41.846587+00:00
-- url     : https://prove2.me/theorems/dcb02360-535b-46df-ac9d-5621a679367a
-- title:
--   Deferred decisions for a finite adaptive reveal rule
-- statement:
--   Consider a countable independent Boolean array with possibly different coordinate laws. A nonanticipating rule observes a finite random set of coordinates and chooses a fresh coordinate whose success probability is always $p$. If an event $E$ is determined by the observed coordinates on each reveal-and-choice case, then $$\Pr(E\cap\{X_{\mathrm{next}}=1\})=p\Pr(E).$$ The formal hypotheses explicitly require that each reveal-and-choice case is determined by its revealed set; this makes the next-coordinate selection nonanticipating.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.adaptive_fresh_observed {ι : Type*} [Countable ι] [DecidableEq ι]
    (κ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (κ i)] (p : ℝ≥0∞)
    (revealed : (ι → Bool) → Finset ι) (next : (ι → Bool) → ι)
    (hfresh : ∀ ω, next ω ∉ revealed ω)
    (hsame : ∀ ω, κ (next ω) {true} = p)
    (E : Set (ι → Bool))
    (hlocal : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      ((revealed ω = S ∧ next ω = a) ↔ (revealed ω' = S ∧ next ω' = a)))
    (hobserved : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      (revealed ω = S ∧ next ω = a) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) = true} =
      (Measure.infinitePi κ) E * p := by sorry
