-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_capped_lower_grid_clock_tendsto_ws01c
-- name    : AvramDividend.Classical.bv_finite_capped_lower_grid_clock_tendsto_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:48:25.311789+00:00
-- url     : https://prove2.me/theorems/92007001-ecc1-4826-9829-866cab8f32e4
-- title:
--   Finite strict lower-grid prefix clock converges to the true capped strict lower clock
-- statement:
--   For a positive mesh shrinking to zero and a finite prefix whose final grid time exceeds the cap T, the capped strict lower-grid infimum over the finite prefix converges in ENNReal to the canonical strict lower first-exit clock capped at T. This combines the already Proved all-grid lower-clock convergence with the exact finite-prefix cap identity, leaving the lower exit notion unaltered.
-- source:
--   Unchanged substantive theorem from work/avram_ws01c_capped_grid_prefix_identity_draft.lean. The exact dependency bv_lower_grid_cap_eq_finite_prefix_ws01c is now canonically Proved UUID 197c6335-dbba-42c9-bcfe-3e072ba2e4f0, accepted CE-linked repair candidate 17901 submission 8a873514-b622-497c-8df2-c8b4b8974d4d. The all-grid convergence imported chat03_official_lower_grid_clock_tendsto is already Proved. Complete exact statement/proof work/avram_ws01c_finite_capped_grid_tendsto_solution_20261028.lean, no changes to original strict lower clock. Publication repair after terminal job a025049b-6af4-4fbf-918b-2e4e8345067d failed on missing Measure/Filtration/𝓝; added only required namespace openings in preamble and proof source; formal statement preserved byte-for-byte.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_bv_lower_grid_cap_eq_finite_prefix_ws01c

open MeasureTheory Filter Topology Set Order AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_capped_lower_grid_clock_tendsto_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (ω : Ω) (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    Tendsto
      (fun n : ℕ =>
        (⨅ (k : ℕ) (_ : k ≤ M n),
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞) ⊓
          (T : ℝ≥0∞))
      atTop
      (𝓝 (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞))) := by sorry
