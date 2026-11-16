-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite_jump_drift_deficit_telescope
-- name    : AvramDividend.Classical.avram_bv_finite_jump_drift_deficit_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:33:52.145199+00:00
-- url     : https://prove2.me/theorems/7ade95e5-a1bc-4c0d-922c-b9c53dc34784
-- title:
--   Finite-jump piecewise-drift path telescoping over actual jumps
-- statement:
--   A finite-jump real-valued path starts at zero and has constant drift-adjusted deficit on every interval free of jumps. Its full drift deficit at T equals the finite sum of the actual downward jump sizes on (0,T]. This is deterministic, independent of Lévy standing assumptions, and isolates the finite-jump telescoping argument.
-- source:
--   Finite variation càdlàg path decomposition; Protter (2005) Chapter II §7, integration by parts for finite variation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite_jump_drift_deficit_telescope
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (h0 : f 0 = 0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    (∑' t : ℝ≥0, if 0 < t ∧ t ≤ T then
      Function.leftLim f t - f t else 0) =
      (T : ℝ) * drift - f T := by sorry
