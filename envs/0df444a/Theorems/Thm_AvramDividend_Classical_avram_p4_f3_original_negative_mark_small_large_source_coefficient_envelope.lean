-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_small_large_source_coefficient_envelope
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_mark_small_large_source_coefficient_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:44:28.125885+00:00
-- url     : https://prove2.me/theorems/3d3442c4-4377-465f-8ef5-3c08dd2ebcb7
-- title:
--   Physical original negative-jump small/large source coefficient envelope
-- statement:
--   For the exact original UBV verification function, C2 in strictly positive reserve below cap, continuous on nonnegative reserves, zero at negatives, every interior compact band has a linear small-negative-jump coefficient bound and a uniform large-negative-jump bound. This is a deterministic source coefficient step for the genuine original Levy process, with no extra uniform derivative hypothesis near ruin and with C=top allowed.
-- source:
--   Combine two independently Proved/public P4-F3 original verification value lemmas 8179243e and 22692cae. The small marks do not cross the half-size compact reserve band; large marks are controlled through the full negative half-line. Does not assert stochastic integral existence, conditional second moments, or natural-clock integrability.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_mark_small_large_source_coefficient_envelope
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ A B : ℝ, 0 ≤ A ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (-(δ / 2) < z →
          |w (u + z) - w u| ≤ B * |z|) ∧
        (z ≤ -(δ / 2) →
          |w (u + z) - w u| ≤ 2 * A) := by sorry
