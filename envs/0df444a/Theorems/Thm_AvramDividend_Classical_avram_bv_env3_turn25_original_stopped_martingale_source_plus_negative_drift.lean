-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
-- name    : AvramDividend.Classical.avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:58:11.359211+00:00
-- url     : https://prove2.me/theorems/71b27d5a-8ee2-4c40-a255-90024a93f8d8
-- title:
--   Actual clock-stopped original source martingale plus nonpositive HJB drift
-- statement:
--   For the original spectrally negative Lévy filtration and genuine stopped martingale Y, a chronological physical-grid sum of Y increments plus nonpositive integrable drift B_i, each included only when the original stopping clock tau has not yet occurred, is integrable with nonpositive expectation. This makes the original source martingale and stopping-time assumptions explicit, yielding an original-process signed grid inequality.
-- source:
--   Source-verified adapters BV-ENV3 turns 22 and 24; conditional centering via Martingale.condExp_ae_eq and predictable stopping event via IsStoppingTime. Both child prerequisites must be Proved before solution import; no hypothetical martingale Y is constructed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (B : ℕ → Ω → ℝ)
    (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then
        (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) ∂P) ≤ 0 := by sorry
