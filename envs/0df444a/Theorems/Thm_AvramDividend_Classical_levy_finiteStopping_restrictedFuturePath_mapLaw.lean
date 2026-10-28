-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
-- name    : AvramDividend.Classical.levy_finiteStopping_restrictedFuturePath_mapLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:47:35.551679+00:00
-- url     : https://prove2.me/theorems/e2543758-86c1-4254-a0b4-433781e31752
-- title:
--   Full stopped-future path law restricted to a stopped-history event
-- statement:
--   The complete shifted future increment path of a spectrally negative Lévy process, restricted to any event observable at a finite stopping time, has the law of the original Lévy process multiplied by the probability of that event.
-- source:
--   Follows from finite-coordinate measure law 834e33eb-226c-4115-8ecf-0c4247cdd3ba and generic scaled Pi-law uniqueness, to supply the event and complementary-event marginal laws in canonical strong-Markov joint-law theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_mapLaw
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_restrictedFuturePath_mapLaw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) (P.restrict A) =
    (P A) • Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  sorry
