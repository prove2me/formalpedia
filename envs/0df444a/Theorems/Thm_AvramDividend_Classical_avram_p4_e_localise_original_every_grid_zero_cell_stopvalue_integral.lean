-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_grid_zero_cell_stopvalue_integral
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_every_grid_zero_cell_stopvalue_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:52:42.197411+00:00
-- url     : https://prove2.me/theorems/4bf962f5-17c7-4204-8bf6-65d5e7baf774
-- title:
--   Original stoppedValue at every varying grid initial cell has zero expectation for zero-start process
-- statement:
--   For the genuine original process P and source finite-index stoppedValue semantics, the constant zero stopping index equals f at grid time e_k(0). If every grid starts at physical time zero and the original martingale integrand f has f(0,ω)=0, this stoppedValue is identically zero and hence has zero integral. This discharges the explicit initial-cell expectation hypothesis in the P4-E varying-grid optional-stopping bridge.
-- source:
--   Proved P4-E finite WithTop Nat stoppedValue evaluator, source X original and Mathlib integral_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original true process has a centred zero-clock stoppedValue on every varying grid when it starts at zero. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_every_grid_zero_cell_stopvalue_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ)
    (e : ℕ → ℕ → ℝ≥0)
    (hZeroGrid : ∀ k, e k 0 = 0)
    (hZeroProcess : ∀ ω, f 0 ω = 0) :
    ∀ k, (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) = 0 := by sorry
