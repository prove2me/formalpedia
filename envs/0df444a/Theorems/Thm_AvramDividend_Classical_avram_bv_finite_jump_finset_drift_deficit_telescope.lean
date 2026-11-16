-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite_jump_finset_drift_deficit_telescope
-- name    : AvramDividend.Classical.avram_bv_finite_jump_finset_drift_deficit_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:46:20.395202+00:00
-- url     : https://prove2.me/theorems/ce7731bf-537e-4dc5-af16-2d2baa10def0
-- title:
--   Finite chronological jump Finset telescoping of piecewise-drift path
-- statement:
--   For a path with finitely many genuine jumps in (0,T], starting at zero and evolving with slope drift between jumps, the drift deficit at T equals the ordinary Finset sum of actual downward jumps. This is the finite chronological source identity underlying the original pathwise Lévy-Itô jump series.
-- source:
--   Protter (2005) finite variation chain rule, finite-activity deterministic jump decomposition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite_jump_finset_drift_deficit_telescope
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (h0 : f 0 = 0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    Finset.sum hFinite.toFinset
      (fun t => Function.leftLim f t - f t) =
      (T : ℝ) * drift - f T := by sorry
