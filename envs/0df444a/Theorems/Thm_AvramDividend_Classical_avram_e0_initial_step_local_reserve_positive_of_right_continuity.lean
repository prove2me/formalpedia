-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_local_reserve_positive_of_right_continuity
-- name    : AvramDividend.Classical.avram_e0_initial_step_local_reserve_positive_of_right_continuity
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-07T19:28:30.004983+00:00
-- url     : https://prove2.me/theorems/f6cbd410-e5e3-422d-94fd-1edc9a072923
-- title:
--   Positive original reserve interval after an affordable initial dividend from right-continuity
-- statement:
--   For the original Avram source process, a strictly affordable initial lump-sum leaves a locally nonnegative reserve at every sufficiently small time whenever its path is continuous at the origin and its initial value is zero. This supplies the local-reserve hypothesis of the proved positive-ruin-time lemma.
-- source:
--   Positive-ruin-time criterion 8ff20e24 and initial-right-limit theorem 7fa270ec.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_step_local_reserve_positive_of_right_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      rightLimit (fun s η => if s = 0 then 0 else K η) t ω = K ω)
    (hzero : X.X 0 ω = 0)
    (hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
    (hgap : K ω < x) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω := by sorry
