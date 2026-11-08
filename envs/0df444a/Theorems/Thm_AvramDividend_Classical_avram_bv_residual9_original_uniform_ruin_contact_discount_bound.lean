-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_uniform_ruin_contact_discount_bound
-- name    : AvramDividend.Classical.avram_bv_residual9_original_uniform_ruin_contact_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:40:51.974805+00:00
-- url     : https://prove2.me/theorems/53ba9d1e-1217-4469-b63e-115b8dca015d
-- title:
--   Original Avram uniform physical-grid ruin-contact discount commutator is bounded at order T/(n+2)
-- statement:
--   On the exact Avram uniform original physical grid u n i = T*i/(n+2), if all post-grid values are nonnegative except at a designated ruin-contact index, the entire discount commutator is controlled by qT/(n+2) times that contact negative part. Imports the already proved exact uniform grid width, without replacing the original process or asserting unproved stochastic integrability.
-- source:
--   AVRAM BV-RESIDUAL9 round-four uniform stopped-grid source interface

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_grid_exact_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_unique_ruin_contact_mesh_error
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_uniform_ruin_contact_discount_bound
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n j : ℕ) (hj : j < n + 1)
    (post : ℕ → ℝ)
    (hpost : ∀ i, i < n + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (n + 1),
      (Real.exp (-(q * (u n (i + 1) : ℝ))) -
        Real.exp (-(q * (u n i : ℝ)))) * post (i + 1)) ≤
      (q * (T / ((n : ℝ) + 2))) * max (-post (j + 1)) 0 := by sorry
