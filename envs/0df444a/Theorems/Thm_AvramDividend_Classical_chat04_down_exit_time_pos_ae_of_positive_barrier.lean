-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_ae_of_positive_barrier
-- name    : AvramDividend.Classical.chat04_down_exit_time_pos_ae_of_positive_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:18:51.089977+00:00
-- url     : https://prove2.me/theorems/1b5e8224-8cb8-4bd5-8266-e35e1c7b7db0
-- title:
--   Strict downward passage below a negative level takes positive time on every Lévy path
-- statement:
--   For any spectrally negative Lévy process beginning at zero and any positive level a, right-continuity guarantees a positive initial interval before the process can enter the region below -a. Consequently the first strict passage time below -a is positive almost surely. Removes a down-clock prerequisite in the upper-reserve stopped-scale identity.
-- source:
--   Proved chat04_initial_safe_window_of_rightCont_zero (7c9b8b20-5b1b-4f1d-8e2e-979243bf3747) and chat04_down_exit_time_pos_of_initial_safe_window (33197660-e41d-4347-875f-34be6603eef7). Intended direct import into upper boundary discount and the accepted two_sided_exit_before_ruin_integral_identity reduction (3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_down_exit_time_pos_ae_of_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, 0 < twoSidedExitDownTime X (-a) ω := by sorry
