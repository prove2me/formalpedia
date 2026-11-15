-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_rejection_uniform_slice_mass
-- name    : AppliedSDE.SarkkaSolin.rejection_uniform_slice_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:34:19.132056+00:00
-- url     : https://prove2.me/theorems/a7eadc79-c96a-483b-9d1e-66cc86640059
-- title:
--   Uniform acceptance mark yields its threshold mass
-- statement:
--   Supporting theorem for exact rejection sampling in Sarkka and Solin (2019), Chapter 8; required by AppliedSDE.SarkkaSolin.exact_rejection_sampling_accepted_law.
-- source:
--   Sarkka and Solin (2019), Algorithm 8.23. Parent theorem abc82f18-47fe-43a7-853c-18d275099080.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.rejection_uniform_slice_mass
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ((volume : Measure ℝ).restrict (Set.Icc 0 1)) (Set.Iic w) =
      ENNReal.ofReal w := by
  sorry
