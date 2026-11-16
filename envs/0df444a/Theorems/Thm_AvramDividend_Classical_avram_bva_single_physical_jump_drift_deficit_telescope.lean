-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_single_physical_jump_drift_deficit_telescope
-- name    : AvramDividend.Classical.avram_bva_single_physical_jump_drift_deficit_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:45:53.836207+00:00
-- url     : https://prove2.me/theorems/79e9d71e-93cf-440a-81d0-1c880c33ea4a
-- title:
--   Single original physical jump finite-variation drift telescope
-- statement:
--   If a path starts at zero and has exactly one possible physical jump at a>0 before T, and its drift-adjusted deficit remains constant across all jump-free intervals, then its full drift deficit at T equals the exact original downward jump at a. This provides the one-jump induction case of the finite-activity Lévy-Ito chronological telescope.
-- source:
--   Finite-activity original-path drift evolution, actual jump at a and leftLimit affine lemma

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_single_physical_jump_drift_deficit_telescope
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T a : ℝ≥0)
    (h0 : f 0 = 0) (ha : 0 < a) (haT : a ≤ T)
    (hOnly : ∀ u ∈ Set.Ioc (0 : ℝ≥0) T,
        f u - Function.leftLim f u ≠ 0 → u = a)
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    Function.leftLim f a - f a = (T : ℝ) * drift - f T := by sorry
