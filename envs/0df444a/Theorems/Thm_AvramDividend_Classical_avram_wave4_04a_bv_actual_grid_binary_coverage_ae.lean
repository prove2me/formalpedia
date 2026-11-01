-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_binary_coverage_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_binary_coverage_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:47:56.983931+00:00
-- url     : https://prove2.me/theorems/24835df1-d55e-47ae-8ade-f0896e421993
-- title:
--   Every original bounded-variation Lévy grid cell is drift-only or strictly jump-active almost surely
-- statement:
--   For any monotone deterministic schedule of the actual BV spectrally negative Lévy source X, all finitely many grid cells are simultaneously classified on one full-probability event as either a strict deficit relative to drift or exactly drift-only. This rules out a third over-drift event and supplies the genuine source-process full-coverage condition missing from an already Proved complete-pattern binomial law. Uses the canonical source drift-increment bound on all schedule pairs.
-- source:
--   Avram–Palmowski–Pistorius (2007), bounded-variation compound-Poisson grid reduction. Proved actual drift pair inequality 931205fa-e220-4a44-9add-9f4af3cb4704, required for Open source grid binomial law ebded8db-bbd8-4a6c-9fc4-220f56f7b51e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_schedule_pairs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_binary_coverage_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, i < n →
      (X.X (t (i + 1)) ω - X.X (t i) ω <
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))) ∨
      (X.X (t (i + 1)) ω - X.X (t i) ω =
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))) := by sorry
