-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_real_toNNReal_measurable_explicit_ws01c
-- name    : AvramDividend.Classical.bv_real_toNNReal_measurable_explicit_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:22:50.931229+00:00
-- url     : https://prove2.me/theorems/4e6ab162-435e-4a00-95f9-b07368548347
-- title:
--   The nonnegative-part clock map is measurable
-- statement:
--   The real-to-nonnegative-real truncation is measurable. The proof constructs it as the measurable subtype map x↦⟨max(0,x),0≤max(0,x)⟩. Used to compose joint Lévy path measurability with shifted positive times.
-- source:
--   Causal repair of terminal job 1b1f6a59-dc89-4611-a744-653cd7194ed9, whose preamble failed to parse ℝ≥0 as NNReal (LE Type, OfNat Type 0). Import Mathlib and open scoped NNReal while preserving the exact statement. The original 17-line proof with matching preamble is work/avram_ws01c_tonnreal_meas_solution_pub_repair_20261028.lean.

import Mathlib

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.bv_real_toNNReal_measurable_explicit_ws01c :
    Measurable (Real.toNNReal : ℝ → ℝ≥0) := by sorry
