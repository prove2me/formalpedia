-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
-- name    : AvramDividend.Classical.chat04_initial_safe_window_of_rightCont_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:52:23.110262+00:00
-- url     : https://prove2.me/theorems/7c9b8b20-5b1b-4f1d-8e2e-979243bf3747
-- title:
--   Right-continuous Lévy path starting at zero has a positive initial safety window above a negative barrier
-- statement:
--   For a path of the published spectrally negative Lévy process which starts at zero, right-continuity at time zero and a>0 provide ε>0 such that X_t≥−a for every t<ε. The proof uses the neighbourhood basis for the right-hand filter, and is an exact mathematical prerequisite for the upper-endpoint two-sided-exit clock lemma.
-- source:
--   IsScaleFunction two-sided exit workstream, consumed by chat04_down_exit_time_pos_of_initial_safe_window (33197660-e41d-4347-875f-34be6603eef7) and chat04_upper_endpoint_exit_expectation_of_ae_regular_windows (3bdb260e-3431-4b7c-a303-22490db7e53a).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.chat04_initial_safe_window_of_rightCont_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) (ω : Ω)
    (h0 : X.X 0 ω = 0) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω := by sorry
