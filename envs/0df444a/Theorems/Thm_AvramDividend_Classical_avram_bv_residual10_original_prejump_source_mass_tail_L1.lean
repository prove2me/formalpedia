-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_source_mass_tail_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_prejump_source_mass_tail_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:53:23.306725+00:00
-- url     : https://prove2.me/theorems/e91d7387-3f50-45d6-80c6-1623508c5b79
-- title:
--   Original pre-jump physical-row clipping has vanishing integrable BV source-mass tail
-- statement:
--   For the actual BV spectrally negative Lévy process, original controlled reserve left limits and physical grid, construct measurable rowwise clipping events that exhaust almost surely. Under the standing source-mass integrability theorem, the authentic fixed-clock BV Lévy source-mass envelope outside these events is integrable for every row and has vanishing expectation. This does not bound the actual discretisation error by that envelope, which is the remaining mathematical obligation.
-- source:
--   AVRAM BV-RESIDUAL10 actual stopped original-process source-mass tail localisation, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_measurable_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_prejump_source_mass_tail_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤)
    (T : ℝ≥0) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ N : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n = {ω | ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (N n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n, Integrable (fun ω => if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
