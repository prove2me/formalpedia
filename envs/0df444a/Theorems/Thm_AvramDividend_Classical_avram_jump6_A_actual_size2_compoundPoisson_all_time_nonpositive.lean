-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_size2_compoundPoisson_all_time_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_A_actual_size2_compoundPoisson_all_time_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:43:37.707649+00:00
-- url     : https://prove2.me/theorems/8cca76a0-9130-434f-912f-5cfe8fc1eebf
-- title:
--   Actual negative size-two compound Poisson path never increases the original reserve
-- statement:
--   For the actual rate-one compound Poisson driver with Lévy mark law δ−2, every physical mark equals −2 almost surely, and the original compoundPoisson(0) path at any real time is -2 times its nonnegative jumpCount. Consequently the entire real-time physical jump path is nonpositive simultaneously almost surely. This is a genuine original-process source needed to show the finite-cap barrier remains dormant throughout a short Brownian tube before the first ruin-causing negative jump, without assuming a synthetic noise model.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_size2_compoundPoisson_all_time_nonpositive
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      compoundPoisson (0 : ℝ) τ Y t ω ≤ 0 := by sorry
