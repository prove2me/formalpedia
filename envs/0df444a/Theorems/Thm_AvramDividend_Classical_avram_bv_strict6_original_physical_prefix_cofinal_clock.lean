-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_physical_prefix_cofinal_clock
-- name    : AvramDividend.Classical.avram_bv_strict6_original_physical_prefix_cofinal_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:29:27.888117+00:00
-- url     : https://prove2.me/theorems/b4799e97-ff73-46d3-8977-8c61f6eace1d
-- title:
--   Original BV strict-prefix stopped-cell clock is monotone and cofinal
-- statement:
--   The actual original strict-prefix stopping grid reaches the clocks T-T/(n+2) before a positive deterministic horizon T. These clocks are nonnegative, bounded by T, increase with refinement, and eventually exceed every strictly pre-horizon real time, allowing monotone Stieltjes cash cofinal passage. The proof derives the exact cofinality from the accepted delta clock certificate, with no additional process regularity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_natural_inner_clock_delta_certificate
open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_original_physical_prefix_cofinal_clock
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let v : ℕ → ℝ := fun n => T - δ n
    Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < v n) := by sorry
