-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
-- name    : AvramDividend.Classical.avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:26:17.865956+00:00
-- url     : https://prove2.me/theorems/587d4dfd-7161-4fc3-86d6-1c1966a0e359
-- title:
--   True-stop physical Gaussian centred large-tail energy sum is measurable from nonzero-volatility normalised increments
-- statement:
--   Measurability of the original Gaussian source increment after division by nonzero volatility implies measurability of its true-stop masked finite-grid large-tail squared-energy sum, without requiring extra hypotheses.
-- source:
--   Discharges original ga_a52 source hSumMeas using ga_a54 and original normalised increment hMeas from ga_a41.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (Z : ℕ → Ω → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (hNormMeas : ∀ i ∈ S,
      Measurable (fun ω : Ω => Z i ω / σ))
    (η : ℝ) :
    Measurable (fun ω : Ω =>
      Finset.sum S (fun i =>
        if s i < ρ ω then
          ENNReal.ofReal (if η ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0)) := by sorry
