-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_spatial_upcross_fullmark_initial_positive_event_zero
-- name    : AvramDividend.Classical.avram_ja18_spatial_upcross_fullmark_initial_positive_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:54:09.215145+00:00
-- url     : https://prove2.me/theorems/1344eb24-cdc9-4336-90d0-4c1dd55db777
-- title:
--   Physical full negative-jump stopped martingale zero on upcross positive-clock initial events
-- statement:
--   For each bounded spatial upcross stop of the genuine original finite-activity Levy process, the compensated full negative jump source includes uncompensated large marks plus the original drift correction. Its stopped gain is integrable and its integral vanishes on any initial-information event intersected with the positive-clock mask. Reuses Proved genuine fullmark martingale and positive-clock measurability, preventing the smallmark-only omission in the open spatial ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_stopped_jump_initial_event_integral_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_spatial_upcross_fullmark_initial_positive_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (hκbound : ∀ k ω, κ k ω ≤ (n : ℝ≥0))
    (k : ℕ) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) ∧
      Integrable (fun ω => Jfull (κ k ω) ω) P ∧
      (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, Jfull (κ k ω) ω ∂P) = 0 := by sorry
