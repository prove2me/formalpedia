-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
-- name    : AvramDividend.Classical.avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:07:35.66033+00:00
-- url     : https://prove2.me/theorems/47d6d44f-a89e-44a1-b14c-17f9f28cc5c6
-- title:
--   Original BV C1 verification candidate has a finite uniform global negative-to-cap value bound from source smoothness and zero extension
-- statement:
--   For the actual classical dividend verification candidate w, continuous on nonnegative reserves and zero on negative reserves as required by the corrected original BV verification theorem, show that below any finite reserve ceiling b≥0 there exists a finite nonnegative R with ‖w(v)‖≤R for every v≤b. The compact positive portion [0,b] is bounded by original candidate continuity and the negative portion is identically zero. This directly discharges the previously free global value-bound hypothesis in all original large-source-mark and ruin overshoot integrability arguments.
-- source:
--   Pinned exact Mathlib IsCompact.exists_bound_of_continuousOn and genuine classical-dividend candidate continuity and zero-extension assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → ‖w v‖ ≤ R := by sorry
