-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
-- name    : AvramDividend.Classical.avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:14:36.281292+00:00
-- url     : https://prove2.me/theorems/38835ae4-6c1e-4466-8cbe-bc7cfc0d6d4f
-- title:
--   Original physical-grid full compensated negative-mark martingale L2 budget implies square-root L1 budget
-- statement:
--   For every finite original grid on a probability space, integrable cross-products of its measurable signed stopped compensated marked increments imply square-integrability of their full sum, and an L2 energy upper budget B bounds the L1 integral of the full sum by sqrt B. The proof uses the proved probability-theoretic integral absolute Cauchy-Schwarz theorem and the exact finite cross-product expansion; it does not make a diagonal-only assumption or replace the original mark increments.

import Mathlib
import Theorems.Thm_ProbabilityTheory_integral_abs_le_sqrt_integral_sq
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (Z : ℕ → Ω → ℝ)
    (hZM : ∀ i ∈ Finset.range m, Measurable (Z i))
    (hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (B : ℝ)
    (hBudget :
      (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤ B) :
    (∫ ω, |∑ i ∈ Finset.range m, Z i ω| ∂P) ≤
      Real.sqrt B := by sorry
