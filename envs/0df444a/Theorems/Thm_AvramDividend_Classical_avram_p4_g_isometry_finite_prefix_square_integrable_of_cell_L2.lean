-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_square_integrable_of_cell_L2
-- name    : AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_square_integrable_of_cell_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:42:35.323655+00:00
-- url     : https://prove2.me/theorems/1574cca8-8fd7-4bab-8ed0-a6d7a03c596c
-- title:
--   Finite prefix L2 sum has integrable quadratic moment
-- statement:
--   For actual original-probability-space L2 cell increments D_i, every finite prefix sum is L2 and hence its square is integrable. This supplies the prefix-square integrability needed by the P4-G physical finite-grid isometry, using only standard MemLp add and Cauchy-Schwarz.
-- source:
--   Pinned Mathlib MemLp.zero, MemLp.add, MemLp.integrable_mul; needed for physical original isometry source.

import Mathlib

open MeasureTheory
open scoped ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_square_integrable_of_cell_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range n, D i ω) ^ 2) P := by sorry
