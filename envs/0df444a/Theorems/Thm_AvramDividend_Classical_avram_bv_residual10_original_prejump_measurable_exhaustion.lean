-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_measurable_exhaustion
-- name    : AvramDividend.Classical.avram_bv_residual10_original_prejump_measurable_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:47:22.783663+00:00
-- url     : https://prove2.me/theorems/ac1e5301-3ce5-4c14-8283-b89781d45306
-- title:
--   Original pre-jump reserve clipping gives measurable almost-surely exhausting physical-row events
-- statement:
--   For the actual original bounded-variation dividend-control setup and a deterministic physical grid, construct measurable coefficient-clipping events that eventually contain almost every sample path when the discarded-error tolerances are summable. This directly provides the measurable-event and almost-sure-exhaustion interfaces needed by the pre-existing Avram positive-error transfer theorem 2a06bf39, without asserting its remaining uniform tail or local expected-error hypotheses.
-- source:
--   AVRAM BV-RESIDUAL10 original pre-jump measurable exhaustion interface, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_row_ae_clipping

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_prejump_measurable_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n = {ω | ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (K n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by sorry
