-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
-- name    : AvramDividend.Classical.avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:08:27.604169+00:00
-- url     : https://prove2.me/theorems/8b3e96b4-82f4-47e4-86e1-37b33d1399e8
-- title:
--   Patching an F0-measurable conull continuous event preserves the original raw adaptation and yields allpath continuity
-- statement:
--   An adapted zero-start real process with continuous paths on a conull event measurable in the original initial sigma-algebra admits an allpath continuous adapted modification on the unchanged filtration by replacing its values by zero on the exceptional event.
-- source:
--   Original raw filtration monotonicity and Mathlib measurability under piecewise definition.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- An initial-sigma-algebra conull good-path event permits an all-path adapted regularisation. -/

theorem AvramDividend.Classical.avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t, Measurable[𝓕 t] (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (E : Set Ω)
    (hE : MeasurableSet[𝓕 0] E)
    (hAE : ∀ᵐ ω ∂P, ω ∈ E)
    (hGood : ∀ ω ∈ E, Continuous (fun t : ℝ≥0 => G t ω)) :
    ∃ H : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (H t)) ∧
      (∀ ω, H 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, H t ω = G t ω) ∧
      (∀ ω, Continuous (fun t : ℝ≥0 => H t ω)) := by sorry
