-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_negative_extension_and_nonnegative_continuity_allow_nonzero_ruin_payoff
-- name    : AvramDividend.Classical.avram_wave6_04_negative_extension_and_nonnegative_continuity_allow_nonzero_ruin_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:04:29.632193+00:00
-- url     : https://prove2.me/theorems/d22435eb-f092-44a1-81a9-1451fe0818c9
-- title:
--   Original endpoint assumptions permit a nonzero payoff at ruin despite zero negative extension
-- statement:
--   Exhibit a real-valued payoff w, continuous on [0,∞) and zero on strictly negative reserves, with w(0)=1. This proves that the original negative extension and nonnegative continuity assumptions do not imply w(0)=0, so the Itô–Meyer generator must distinguish exact zero landing from strict ruin overshoot.
-- source:
--   Wave6 Chat04 explicit original source endpoint-assumption counterexample, guarding against invalid w(0)=0 inference.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_negative_extension_and_nonnegative_continuity_allow_nonzero_ruin_payoff :
    ∃ w : ℝ → ℝ,
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      w 0 = 1 := by sorry
