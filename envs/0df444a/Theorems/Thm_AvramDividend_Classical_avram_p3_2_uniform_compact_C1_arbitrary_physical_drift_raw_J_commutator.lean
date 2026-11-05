-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator
-- name    : AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:24:57.255186+00:00
-- url     : https://prove2.me/theorems/efcb09a1-d2a0-47d1-8d90-b231515b0c57
-- title:
--   Uniform C1 physical drift vs raw-J mixed commutator for arbitrary source shifts
-- statement:
--   The true original source cash decomposition requires an independent physical drift shift. By derivative uniform continuity on one strict interior reserve band, arbitrary drift c with |c| sufficiently small makes the nonlinear difference across any original raw-J jump segment at most ε times its jump size. The deterministic uniform bound is independent of the F2 theorem's hard-coded jump-removed Y increment and uses only local C1 assumptions valid under the canonical P3 hypotheses.
-- source:
--   Exact accepted F2 compact C1 derivative proof, stripped to its universal mathematical form with arbitrary z,c,j.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z c j : ℝ,
        Set.uIcc (z - j) z ⊆ Set.Icc a b →
        Set.uIcc (z + c - j) (z + c) ⊆ Set.Icc a b →
        |c| < δ →
        |w (z + c - j) - w (z + c) -
          w (z - j) + w z| ≤ ε * |j| := by sorry
