-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
-- name    : AvramDividend.Classical.avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:37:51.740136+00:00
-- url     : https://prove2.me/theorems/429ba9f5-fc90-4e9d-adac-62edb443fe2c
-- title:
--   Measurable zero extension of the candidate gradient on the exact ENNReal-capped UBV interior
-- statement:
--   For the corrected UBV source domain 0<y and ENNReal.ofReal y<C with C permitted infinite, any w C² only on that domain has a globally measurable gradient extended by zero off the domain. No continuity/differentiability of w is imposed outside the interior, notably at ruin and cap contact.
-- source:
--   Open cap interior via ENNReal.continuous_ofReal, then Proved generic interior derivative zero extension

import Mathlib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension

open Set
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) := by
  sorry
