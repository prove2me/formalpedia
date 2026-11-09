-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat25_topcap_candidate_nonnegative_global
-- name    : AvramDividend.Classical.avram_chat25_topcap_candidate_nonnegative_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:32:41.662926+00:00
-- url     : https://prove2.me/theorems/ddbce92d-90b1-41f9-abb0-60455e708f17
-- title:
--   Infinite-cap C1 gradient and nonnegative boundary imply nonnegative candidate everywhere
-- statement:
--   For a general infinite-cap original Avram test candidate with nonnegative boundary value, positive interior derivative, continuous nonnegative-axis restriction and zero extension below zero, prove global nonnegativity. The source-exact precursor to finite-rate generator increment lower bounds.
-- source:
--   Direct specialization of Proved cb439447-a20c-4328-b137-88d209abc249 to C=top, using w=0 on negative arguments.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
open Set
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat25_topcap_candidate_nonnegative_global
    (C : ℝ≥0∞) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ w y := by sorry
