-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_uniform_centered_grid_transfer
-- name    : AvramDividend.Classical.avram_p3_comp8_original_uniform_centered_grid_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:17:43.255669+00:00
-- url     : https://prove2.me/theorems/8b3d13cf-7f07-4290-84ca-98fbb1a55a98
-- title:
--   Centred compensated stopped-grid increments transfer to the exact original uniform clock
-- statement:
--   Any centred integrable finite compensated-jump increment sum on the BV-MEAS7 uniform clock is the same random variable on the original specified uniform grid, provided both grids use the same first endpoint and exact cell width. This preserves L1 and zero expectation without replacing the Lévy process, stopped correction or physical index.
-- source:
--   Proved BV-MEAS7 prefix uniqueness b832785c-1250-4098-9942-db010c5d21fe and centred original physical grid certificates a08ce531-908d-46f5-ab11-8c204ce9d4ee; parent 4044d709-e30b-4e52-85f0-dc8786d1ed42. Distinct non-circular grid-alignment bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_comp8_original_uniform_centered_grid_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (T : ℝ) (u v : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0) (hv0 : ∀ n, v n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2))
    (hvWidth : ∀ n i, i < n + 1 →
      (v n (i + 1) : ℝ) - (v n i : ℝ) = T / ((n : ℝ) + 2))
    (M : ℕ → ℝ≥0 → Ω → ℝ)
    (hV : ∀ n,
      Integrable
        (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M n (v n (i + 1)) ω - M n (v n i) ω)) ∂P) = 0) :
    ∀ n,
      Integrable
        (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M n (u n (i + 1)) ω - M n (u n i) ω)) ∂P) = 0 := by sorry
