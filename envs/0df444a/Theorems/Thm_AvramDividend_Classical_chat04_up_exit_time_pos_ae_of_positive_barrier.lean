-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_ae_of_positive_barrier
-- name    : AvramDividend.Classical.chat04_up_exit_time_pos_ae_of_positive_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:38:22.40185+00:00
-- url     : https://prove2.me/theorems/a8d9c599-ccaa-4374-a73f-d47bdf3fffa3
-- title:
--   A positive strict upper passage threshold gives positive first passage time almost surely
-- statement:
--   For any spectrally negative Lévy process with a right-continuous path starting at zero, a strictly positive upper crossing threshold b cannot be reached at time zero. A positive initial safe ceiling exists along each path. The first strict upcrossing clock is therefore positive almost surely. This is the previously missing counterpart to positive downward passage, and applies to interior starting reserve 0<x<a with b=a-x.
-- source:
--   Uses Proved chat04_up_exit_time_pos_of_initial_safe_ceiling after publication and the right-continuity field X.rightCont. To be paired with Proved chat04_down_exit_time_pos_ae_of_positive_barrier 1b5e8224 in the interior stopped-scale target 09663d0d.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_of_initial_safe_ceiling
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_up_exit_time_pos_ae_of_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < twoSidedExitUpTime X b ω := by sorry
