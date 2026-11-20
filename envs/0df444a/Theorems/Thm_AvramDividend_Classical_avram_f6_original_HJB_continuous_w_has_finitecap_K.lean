-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_HJB_continuous_w_has_finitecap_K
-- name    : AvramDividend.Classical.avram_f6_original_HJB_continuous_w_has_finitecap_K
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:28:29.847358+00:00
-- url     : https://prove2.me/theorems/75d8e0e4-bed7-4b9f-a660-82823e525dd5
-- title:
--   Continuous original HJB value has a finite local absolute bound on any cap interval
-- statement:
--   From original value function continuousOn Ici 0, every finite cap interval [0,C.toReal] admits a real K bounding |w| throughout. The resulting constant provides the noninvented input to original finite-cap caplinear reward domination.

import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_HJB_continuous_w_has_finitecap_K
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (C : ℝ≥0∞) :
    ∃ K : ℝ, ∀ y : ℝ,
      0 ≤ y → y ≤ C.toReal → |w y| ≤ K := by sorry
