-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_adaptive_fresh_on_event
-- name    : CountingLLL.ReciprocalTest.adaptive_fresh_on_event
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:44:20.672309+00:00
-- url     : https://prove2.me/theorems/e73d5c1b-f42d-44b6-9fcb-626cbf11bc7f
-- title:
--   Deferred decisions when freshness holds on an observed event
-- statement:
--   For an independent countable-valued array, a nonanticipating finite reveal rule chooses a coordinate. Let $E$ be an event determined by the revealed data. If the selected coordinate is fresh and its coordinate event has probability $p$ on $E$, then $$\Pr(E\cap\{X_{\mathrm{next}}\in A_{\mathrm{next}}\})=p\Pr(E).$$ No freshness or equal-probability assumption is needed outside $E$. The formal hypotheses require each reveal-and-choice case and the observed event on that case to be determined by the revealed coordinates.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.adaptive_fresh_on_event {ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (p : ℝ≥0∞)
    (revealed : (ι → α) → Finset ι) (next : (ι → α) → ι)
    (E : Set (ι → α))
    (hfresh : ∀ ω, ω ∈ E → next ω ∉ revealed ω)
    (hsame : ∀ ω, ω ∈ E → κ (next ω) (A (next ω)) = p)
    (hlocal : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      ((revealed ω = S ∧ next ω = a) ↔ (revealed ω' = S ∧ next ω' = a)))
    (hobserved : ∀ S a ω ω', (∀ i ∈ S, ω i = ω' i) →
      (revealed ω = S ∧ next ω = a) → (ω ∈ E ↔ ω' ∈ E)) :
    (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} =
      (Measure.infinitePi κ) E * p := by sorry
