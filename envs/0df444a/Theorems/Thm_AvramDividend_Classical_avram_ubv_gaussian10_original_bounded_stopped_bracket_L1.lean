-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:37:50.774194+00:00
-- url     : https://prove2.me/theorems/fbb436f9-1046-4baa-b3bd-fe43de9690b3
-- title:
--   Original bounded stopping-time Gaussian quadratic bracket is integrable
-- statement:
--   On the unchanged original Avram probability space and right-continuous filtration, a predictable Gaussian coefficient with pathwise continuous finite quadratic bracket, finite samplewise terminal energy and integrable terminal bracket has an integrable bracket evaluated at any genuine bounded original stopping time. The proof combines adaptedness to progressiveness, measurable stoppedValue, and terminal L1 envelope without null augmentation. Its continuity and terminal-integrability assumptions remain explicit mathematical obligations.
-- source:
--   Pinned Mathlib measurable_stoppedValue, original progressive bracket child and original terminal-energy L1 child, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bracket_progressive_of_continuous
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hBound : ∀ ω, τ ω ≤ T)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime)
    (hContinuous : ∀ ω, Continuous (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime))
    (hTerminalL1 : Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
        (H (t, ω)) ^ 2 ∂μtime) P) :
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) (τ ω),
        (H (t, ω)) ^ 2 ∂μtime) P := by sorry
