-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
-- name    : AvramDividend.Classical.avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:54:13.090753+00:00
-- url     : https://prove2.me/theorems/79d11c5d-9a0e-415e-af76-e72c3e2cd592
-- title:
--   The original strictly positive stopped-time event is measurable at the initial right-continuous filtration
-- statement:
--   For the genuine original right-continuous filtration of a spectrally negative Lévy model, any nonnegative stopping clock σ has its event of positive physical time {σ≠0} measurable already at time zero. This is a structural prerequisite for transferring an initial conditional-expectation HJB cash bound to the original strictly positive stopping-clock event A∩{κ_k≠0} in the open parent a4cfaf04 and 1a3d64f9. It uses the exact source IsStoppingTime and no synthetic process or compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by sorry
