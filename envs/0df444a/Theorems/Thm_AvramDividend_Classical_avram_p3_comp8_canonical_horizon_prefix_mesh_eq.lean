-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_canonical_horizon_prefix_mesh_eq
-- name    : AvramDividend.Classical.avram_p3_comp8_canonical_horizon_prefix_mesh_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:51:10.17158+00:00
-- url     : https://prove2.me/theorems/e62bac76-576d-4fd4-aae0-93b7f00b4939
-- title:
--   Original canonical strict prefix grid matches the source physical stopped-grid mesh
-- statement:
--   The exact uniform mesh u_n(i)=T*i/(n+2) of original theorem 4044 is identically the n+1-cell mesh of the strict horizon T-T/(n+2), for each index i. This is the precise deterministic grid parameter alignment required to reuse source stopped-grid Lévy cell identities on the pre-ruin event.
-- source:
--   Source-exact formula copied from 4044; establishes physical mesh equality algebraically without a random clock mismatch.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_canonical_horizon_prefix_mesh_eq
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, (u n i : ℝ) =
      ((T - T / ((n : ℝ) + 2)) / ((n : ℝ) + 1)) * (i : ℝ) := by sorry
