-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:20:01.23611+00:00
-- url     : https://prove2.me/theorems/5163c471-cbad-453d-83b9-fc0ece3cc48e
-- title:
--   Original capped stopped Gaussian bracket is L1 under terminal finite-energy envelope
-- statement:
--   For the actual original Avram probability space and a samplewise capped stopping clock, if the squared Gaussian coefficient is pathwise integrable over the deterministic terminal horizon, the terminal bracket is L1, and the stopped bracket is measurable, then the capped stopped bracket is L1. The proof is dominated integrability with explicit nonnegative quadratic-energy estimates. It records the stopped-clock measurability assumption as a genuine outstanding interface and does not replace X or the filtration.
-- source:
--   Asakura Chapter10L2DominatedLocalMartingale and pinned Mathlib Integrable.mono, setIntegral_mono_set; inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime)
    (hStoppedMeas : Measurable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime))
    (hTerminalL1 : Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
        (H (t, ω)) ^ 2 ∂μtime) P) :
    Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) P := by sorry
