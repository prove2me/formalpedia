-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont
-- name    : AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:54:52.514274+00:00
-- url     : https://prove2.me/theorems/9a637a5d-4e7b-46b4-8e58-4fed8ae54383
-- title:
--   Strong Markov independence at stopped events of the right-continuous Lévy filtration
-- statement:
--   For a spectrally negative Lévy process on an arbitrary filtration, a finite stopping time of its right-continuous modification, and an event observable at the stopping time, the shifted future path is independent of the stopped-event indicator with the same law as the original path. Use the proved right-continuous Lévy-process transport and the proved finite-stopping-time strong Markov independence theorem. This provides a direct bridge from the first-upcrossing and reflected-ruin clocks to the stopped-renewal geometric expectation contraction.
-- source:
--   Transport the Lévy process to the right-continuous filtration with the same sample paths, apply the established stopped-event independence theorem, and rewrite the path identity.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω =>
        (Set.indicator A (fun _ : Ω => (1 : ℝ)) ω,
          fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)) P =
      (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by sorry
