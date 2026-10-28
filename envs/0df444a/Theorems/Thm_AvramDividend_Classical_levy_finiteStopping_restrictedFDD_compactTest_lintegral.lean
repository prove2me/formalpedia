-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_compactTest_lintegral
-- name    : AvramDividend.Classical.levy_finiteStopping_restrictedFDD_compactTest_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:15:22.009735+00:00
-- url     : https://prove2.me/theorems/4a900fdc-a036-471d-bf4d-8e35ed1b2bfa
-- title:
--   Restricted stopped-future finite-coordinate law on compact nonnegative tests
-- statement:
--   For a finite stopping time of a spectrally negative Lévy process and an event measurable in the stopped history, the restricted shifted-increment vector has the same compactly supported continuous nonnegative test integrals as the original path vector, multiplied by the probability of the event.
-- source:
--   Combines the Proved finite-stopping cylinder strong Markov identity 923863b7-543e-4ddf-8e26-f7249d48d98c with the Proved compact-test uniform bound e92f0d3f-6854-4649-8790-12e0c9cbe80b, for the finite-dimensional Riesz law extension and full shifted-path theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_restrictedFDD_compactTest_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hP : P Set.univ ≠ ⊤)
    (J : Finset ℝ≥0)
    (f : CompactlySupportedContinuousMap (J → ℝ) ℝ≥0) :
    (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(Measure.map
      (fun ω : Ω => fun j : J =>
        X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω) (P.restrict A))) =
    P A * (∫⁻ y, ((f (fun j : J => y (j : ℝ≥0)) : ℝ≥0) : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
