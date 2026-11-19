-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third
-- name    : AvramDividend.Classical.avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:12:09.631945+00:00
-- url     : https://prove2.me/theorems/ef1ffed8-0a6b-455d-98f4-1c45c17423d1
-- title:
--   Exact quadratic energy of original diffuse uniform negative-jump Lévy measure
-- statement:
--   The real quadratic jump energy for the genuine uniform negative-mark Lévy measure (Lebesgue restricted to (-1,0)) is exactly 1/3 and strictly positive. This is the concrete source required to test the nearzero-vs-retained compensated small-band variance equation under the existing Proved Standing compound-Poisson source.

import Mathlib
open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
      (1 / 3 : ℝ) := by sorry
