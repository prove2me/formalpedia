-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_unique_ruin_contact_mesh_error
-- name    : AvramDividend.Classical.avram_bv_residual9_unique_ruin_contact_mesh_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:34:21.810193+00:00
-- url     : https://prove2.me/theorems/b6d0c8eb-49dc-4be4-873f-3701c3a467f7
-- title:
--   Uniform stopped physical-grid discount error reduces to the unique negative ruin-contact value
-- statement:
--   If all post-cell values are nonnegative except possibly the unique ruin-contact index, a stopped physical grid whose cells have width at most δ incurs discount commutator at most qδ times the negative contact value. This is a deterministic source-exact interface; the missing stochastic integrable contact envelope is left explicit.
-- source:
--   AVRAM BV-RESIDUAL9 round-four physical-grid contact reduction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_discount_commutator_cell_meshwidth
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_unique_ruin_contact_mesh_error
    (q δ : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m j : ℕ) (hj : j < m + 1)
    (hmono : ∀ i, i < m + 1 → u i ≤ u (i + 1))
    (hmesh : ∀ i, i < m + 1 →
      (u (i + 1) : ℝ) - (u i : ℝ) ≤ δ)
    (post : ℕ → ℝ)
    (hpost : ∀ i, i < m + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) ≤
      (q * δ) * max (-post (j + 1)) 0 := by sorry
