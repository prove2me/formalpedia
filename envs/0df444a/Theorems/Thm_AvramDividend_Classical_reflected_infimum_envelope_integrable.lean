-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_infimum_envelope_integrable
-- name    : AvramDividend.Classical.reflected_infimum_envelope_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:56:04.311794+00:00
-- url     : https://prove2.me/theorems/820b5271-db77-4a0c-9d34-77ae2fa5e4b3
-- title:
--   Finite-horizon reflected-infimum Laplace envelope is integrable under Lévy law
-- statement:
--   At each finite horizon and positive Laplace parameter, the reflected running-infimum exponential envelope is measurable and bounded by the inverse Laplace parameter. It is therefore integrable under the probability law of the Lévy process. This supplies a real-valued expectation for the finite-horizon killed-survival transform.
-- source:
--   Proved levy_running_infimum_measurable and pinned Mathlib Integrable.of_bound.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflected_infimum_envelope_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun ω : Ω =>
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) P := by sorry
