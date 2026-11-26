-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_shifted_agreement
-- name    : AvramDividend.Classical.avram_locmoll_jump_shifted_agreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:45:55.565803+00:00
-- url     : https://prove2.me/theorems/b13c9b7a-663d-4369-a946-75cc7029af37
-- title:
--   Cap extension agrees with original test and its derivative at every supported negative-mark translate
-- statement:
--   Cap extension agrees with original test and its derivative at every supported negative-mark translate
-- source:
--   Avram Proposition 4(i), child of 10e0ec45-30d2-5555-bcde-5adae9d0be9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_jump_shifted_agreement
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (δ y : ℝ)
    (hδ : 0 < δ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hV : ∀ z : ℝ, ENNReal.ofReal z ≤ C → V z = w z) :
    ContDiffOn ℝ 2 V (Ioo 0 y) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), deriv V (y - r) = deriv w (y - r)) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), ∀ z ≤ 0,
      V (y + z - r) = w (y + z - r)) ∧
    (∀ r ∈ Icc (δ / 3) (2 * (δ / 3)), ∀ z < 0,
      SpectrallyNegativeLevy.generatorIntegrand V (y - r) z =
      SpectrallyNegativeLevy.generatorIntegrand w (y - r) z) := by sorry
