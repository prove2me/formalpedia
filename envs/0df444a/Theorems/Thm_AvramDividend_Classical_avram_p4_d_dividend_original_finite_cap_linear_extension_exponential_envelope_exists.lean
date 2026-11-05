-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:36:27.358651+00:00
-- url     : https://prove2.me/theorems/37c190ea-f912-4d9a-b554-3855601bede3
-- title:
--   Original continuous candidate with finite cap has a global exponential growth envelope automatically
-- statement:
--   Combine independently proved compact interval boundedness from original one-sided continuity with a source-exact global linear cap extension estimate. For C finite and w zero below reserve zero, there is K≥0 such that ‖V(z)‖≤K exp z for every real z. No extra growth or derivative boundary condition is assumed, eliminating the envelope hypothesis in the genuine original stopped raw comparison value L1 proof.
-- source:
--   Original P4-F finite-cap/continuity/negative-reserve definitions, new original compact-bound helper and new finite-cap exponential estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z := by sorry
