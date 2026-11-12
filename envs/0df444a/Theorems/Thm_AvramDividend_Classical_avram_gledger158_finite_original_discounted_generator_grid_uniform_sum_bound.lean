-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
-- name    : AvramDividend.Classical.avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:31:39.628384+00:00
-- url     : https://prove2.me/theorems/4c4cb5c1-4539-4b47-a12b-6ac7517bfc1b
-- title:
--   Finite original stopped generator grid bounded by physical horizon times local envelope
-- statement:
--   For the original stopped generator grid, if every active discounted generator residual has a common absolute bound B and its deterministic uniform clock width delta satisfies m delta≤the physical horizon n, then the absolute grid sum is at most n B. This finite arithmetic assembly is used with the source-exact gledger157 original compact residual bound and gledger155 uniform generator-grid envelope.
-- source:
--   Finite sum absolute triangle, each weighted cell bounded by δB and finite-horizon physical clock inequality.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
    (m n : ℕ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hmδ : (m : ℝ) * δ ≤ (n : ℝ))
    (F : ℕ → ℝ) (hF : ∀ i ∈ Finset.range m, |F i| ≤ B) :
    |Finset.sum (Finset.range m) (fun i => δ * F i)| ≤ (n : ℝ) * B := by sorry
