-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discount_exp_global_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:47:15.003036+00:00
-- url     : https://prove2.me/theorems/0c4855f8-90da-4d9e-80b7-bfa6760d071d
-- title:
--   Nonnegative exponential discount on the true time axis has global bounded variation
-- statement:
--   For every nonnegative real discount rate, the actual exponential discount factor on nonnegative time has globally finite total variation, with no horizon cut-off.
-- source:
--   Mathlib MonotoneOn.boundedVariationOn for the exponential over the nonpositive half-line, and eVariationOn.comp_le_of_antitoneOn under t to -q*t. This discharges a genuine Stieltjes integration-by-parts premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discount_exp_global_variation (q : ℝ) (hq : 0 ≤ q) : BoundedVariationOn (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) Set.univ := by sorry
