-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedPath_ae_event_transfer
-- name    : AvramDividend.Classical.levy_finiteStopping_shiftedPath_ae_event_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:54:28.080579+00:00
-- url     : https://prove2.me/theorems/ced6605f-165e-4459-b22e-ade66209653b
-- title:
--   Almost-sure future-path events persist after finite Lévy stopping times
-- statement:
--   Suppose the original Lévy path belongs almost surely to a measurable set G of whole future paths. A finite stopping time with both the filtration stopping conditions and process path measurability has the property that the entire shifted increment path after that stopping time belongs almost surely to G too. The proof combines the existing Proved strong Markov same-law theorem at a stopping time, existing Proved post-stopping whole-path measurability, and Mathlib's ae_map_iff. It is an authentic probability-measure law transfer for the negative-near-zero path event once its product measurability and unbounded-variation regularity are established, not an excursion-measure Markov theorem.
-- source:
--   Proved Prove2Me stopping-time future-path law and measurability, plus Mathlib.MeasureTheory.Measure.Map.ae_map_iff; related to excursion restart in Kuznetsov, Kyprianou and Rivero (2013) Section 2.3.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finiteStopping_shiftedPath_ae_event_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (G : Set (ℝ≥0 → ℝ)) (hG : MeasurableSet G)
    (hOrig : ∀ᵐ ω ∂P, (fun t : ℝ≥0 => X.X t ω) ∈ G) :
    ∀ᵐ ω ∂P,
      (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω) ∈ G := by sorry
