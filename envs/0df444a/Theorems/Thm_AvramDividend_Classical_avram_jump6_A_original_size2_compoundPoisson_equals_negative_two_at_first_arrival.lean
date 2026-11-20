-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_size2_compoundPoisson_equals_negative_two_at_first_arrival
-- name    : AvramDividend.Classical.avram_jump6_A_original_size2_compoundPoisson_equals_negative_two_at_first_arrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:47:52.878379+00:00
-- url     : https://prove2.me/theorems/acbc9a55-2c2f-4b45-9396-aa6aa4af9e17
-- title:
--   Actual negative size-two compound Poisson physical process equals minus two at its first arrival
-- statement:
--   The actual original marked compound Poisson process of rate one and constant negative two marks has total jump value exactly -2 at its first arrival time almost surely. Combine the Proved all-mark-are-size-two theorem, the newly Proved first-arrival jumpCount=1 theorem, and the Proved physical path equals -2 times jumpCount. This is the essential original negative first-jump source for a finite-cap Brownian+Poisson immediate ruin countermodel.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_size2_compoundPoisson_equals_negative_two_at_first_arrival
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      compoundPoisson (0 : ℝ) τ Y (arrival τ 0 ω) ω = -2 := by sorry
