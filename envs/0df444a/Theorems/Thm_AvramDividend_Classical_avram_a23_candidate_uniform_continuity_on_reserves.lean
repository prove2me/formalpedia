-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_candidate_uniform_continuity_on_reserves
-- name    : AvramDividend.Classical.avram_a23_candidate_uniform_continuity_on_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:37:29.266187+00:00
-- url     : https://prove2.me/theorems/93daccec-5395-4d74-8f6f-c069a76e5005
-- title:
--   HJB candidate uniform continuity on finite reserve cap interval
-- statement:
--   Original continuous HJB candidate is uniformly continuous on the compact cap interval, supporting the Gaussian crossing mesh estimates. This follows from Heine-Cantor.
-- source:
--   Cap interval uniform continuity on original reserve domain.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a23_candidate_uniform_continuity_on_reserves
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0)) :
    UniformContinuousOn w (Icc 0 b) := by sorry
