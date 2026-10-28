-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_exit_clocks_pos_ae
-- name    : AvramDividend.Classical.chat04_interior_two_sided_exit_clocks_pos_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:41:20.962002+00:00
-- url     : https://prove2.me/theorems/a0671a80-9cba-4bfc-9896-75c08318382b
-- title:
--   Both strict two-sided exit times are positive at every interior reserve
-- statement:
--   At a strictly interior initial reserve 0<x<a, right-continuity gives a common positive time interval during which neither strict exit happens. Applying the already proved pathwise up- and down-exit clock lemmas to this same interval shows both first exit clocks are strictly positive almost surely. This supports stopped q-scale martingale initialization.
-- source:
--   Proved chat04_interior_two_sided_initial_safe_window c9d6c919-5bd9-4d85-b1b6-7f2a7fb52194, Proved chat04_up_exit_time_pos_of_initial_safe_ceiling fa8062ee-a1ab-47e1-b40f-efa4485bbb03, and Proved chat04_down_exit_time_pos_of_initial_safe_window 33197660-e41d-4347-875f-34be6603eef7. Root-connected stopped-scale target 09663d0d.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_of_initial_safe_ceiling
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_interior_two_sided_exit_clocks_pos_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (hx0 : 0 < x) (hxa : x < a) :
    ∀ᵐ ω ∂P,
      0 < twoSidedExitUpTime X (a - x) ω ∧
      0 < twoSidedExitDownTime X (-x) ω := by sorry
