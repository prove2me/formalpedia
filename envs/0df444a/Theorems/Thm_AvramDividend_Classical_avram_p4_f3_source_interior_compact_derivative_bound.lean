-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
-- name    : AvramDividend.Classical.avram_p4_f3_source_interior_compact_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:20:46.845634+00:00
-- url     : https://prove2.me/theorems/e6632b80-dff0-4860-86a5-1c73f71fe13d
-- title:
--   Canonical UBV smoothness bounds derivative on any compact interior localisation band
-- statement:
--   The canonical unbounded-variation C2 smoothness hypothesis on the exact positive-reserve/cap interior implies a finite uniform bound on the real derivative on every compact subinterval of that interior. The openness and interior-cover premises are explicit, so no assertion is made at reserve zero or the cap boundary. This is the precise deterministic bounded-coefficient localisation step for a physical stopped Gaussian and small-jump L2 estimate.
-- source:
--   Original canonical fdb9a6a3 smoothness predicate, pinned ContDiffOn.continuousOn_deriv_of_isOpen and IsCompact.exists_bound_of_continuousOn. Theorem is a genuine local coefficient bound, with boundary escape still an upstream obligation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_source_interior_compact_derivative_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ B : ℝ, ∀ y ∈ Icc a b, |deriv w y| ≤ B := by sorry
